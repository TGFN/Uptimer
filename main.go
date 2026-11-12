// uptimer - web server giám sát uptime kiểu UptimeRobot (1 file, không cần thư viện ngoài)
//
// Chạy:
//   go build -o uptimer && ./uptimer -seed https://pixpack.onrender.com
//   rồi mở http://localhost:8288  (đăng nhập mặc định: admin / admin)
package main

import (
	"bytes"
	"context"
	"crypto/rand"
	"crypto/subtle"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"log"
	mrand "math/rand"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

const (
	maxChecks    = 4000
	maxIncidents = 50
	keepDays     = 90
)

type Monitor struct {
	ID       string `json:"id"`
	Name     string `json:"name"`
	Type     string `json:"type"`
	URL      string `json:"url"`
	Method   string `json:"method"`
	Interval int    `json:"interval"`
	Timeout  int    `json:"timeout"`
	Retries  int    `json:"retries"`
	Expect   string `json:"expect"`
	Keyword  string `json:"keyword"`
	Paused   bool   `json:"paused"`
	Created  int64  `json:"created"`
}

type Check struct {
	T    int64  `json:"t"`
	Up   bool   `json:"up"`
	Ms   int    `json:"ms"`
	Code int    `json:"code,omitempty"`
	Err  string `json:"err,omitempty"`
}

type Day struct {
	N   int `json:"n"`
	Up  int `json:"u"`
	Ms  int `json:"ms"`
	MsN int `json:"mn"`
}

type Incident struct {
	Start  int64  `json:"start"`
	End    int64  `json:"end"`
	Reason string `json:"reason"`
}

type State struct {
	Monitor
	Status     string          `json:"status"`
	Since      int64           `json:"since"`
	CertExpiry int64           `json:"certExpiry,omitempty"`
	Checks     []Check         `json:"checks"`
	Days       map[string]*Day `json:"days"`
	Incidents  []Incident      `json:"incidents"`

	fails      int
	failStart  int64
	failReason string
}

type Settings struct {
	Title   string `json:"title"`
	Webhook string `json:"webhook"`
	Discord string `json:"discord"`
	TgToken string `json:"tgToken"`
	TgChat  string `json:"tgChat"`
}

type diskState struct {
	Monitors []*State `json:"monitors"`
	Settings Settings `json:"settings"`
	Pass     string   `json:"pass,omitempty"`
}

type Server struct {
	mu       sync.RWMutex
	mons     map[string]*State
	set      Settings
	cancels  map[string]context.CancelFunc
	sessions map[string]struct{}
	dirty    bool
	file     string
	pass     string
	client   *http.Client
}

var notifyClient = &http.Client{Timeout: 10 * time.Second}

func nowMs() int64 { return time.Now().UnixMilli() }

func newID() string {
	b := make([]byte, 6)
	rand.Read(b)
	return hex.EncodeToString(b)
}

func fmtDur(d time.Duration) string {
	s := int(d.Seconds())
	switch {
	case s < 60:
		return fmt.Sprintf("%d giây", s)
	case s < 3600:
		return fmt.Sprintf("%d phút", s/60)
	case s < 172800:
		return fmt.Sprintf("%d giờ %d phút", s/3600, (s%3600)/60)
	}
	return fmt.Sprintf("%d ngày %d giờ", s/86400, (s%86400)/3600)
}

func shortErr(err error) string {
	if errors.Is(err, context.DeadlineExceeded) {
		return "timeout"
	}
	if errors.Is(err, context.Canceled) {
		return "đã dừng"
	}
	var ue *url.Error
	if errors.As(err, &ue) {
		err = ue.Err
		if errors.Is(err, context.DeadlineExceeded) {
			return "timeout"
		}
	}
	m := err.Error()
	if len(m) > 160 {
		m = m[:160]
	}
	return m
}

func parseExpect(s string) func(int) bool {
	type rng struct{ a, b int }
	var rs []rng
	for _, part := range strings.Split(s, ",") {
		part = strings.TrimSpace(part)
		if part == "" {
			continue
		}
		if i := strings.Index(part, "-"); i > 0 {
			a, e1 := strconv.Atoi(strings.TrimSpace(part[:i]))
			b, e2 := strconv.Atoi(strings.TrimSpace(part[i+1:]))
			if e1 == nil && e2 == nil {
				rs = append(rs, rng{a, b})
			}
		} else if a, err := strconv.Atoi(part); err == nil {
			rs = append(rs, rng{a, a})
		}
	}
	if len(rs) == 0 {
		rs = []rng{{200, 399}}
	}
	return func(c int) bool {
		for _, r := range rs {
			if c >= r.a && c <= r.b {
				return true
			}
		}
		return false
	}
}

func normalize(m *Monitor) error {
	m.Name = strings.TrimSpace(m.Name)
	m.URL = strings.TrimSpace(m.URL)
	if m.URL == "" {
		return errors.New("thiếu URL / host")
	}
	switch m.Type {
	case "http", "keyword", "tcp":
	default:
		m.Type = "http"
	}
	if m.Type == "tcp" {
		if _, _, err := net.SplitHostPort(m.URL); err != nil {
			return errors.New("TCP cần dạng host:port")
		}
	} else {
		if !strings.Contains(m.URL, "://") {
			m.URL = "https://" + m.URL
		}
		u, err := url.Parse(m.URL)
		if err != nil || u.Host == "" || (u.Scheme != "http" && u.Scheme != "https") {
			return errors.New("URL không hợp lệ")
		}
	}
	if m.Type == "keyword" {
		m.Keyword = strings.TrimSpace(m.Keyword)
		if m.Keyword == "" {
			return errors.New("thiếu từ khoá cần tìm")
		}
	}
	if m.Name == "" {
		m.Name = m.URL
	}
	m.Method = strings.ToUpper(m.Method)
	if m.Method != "HEAD" || m.Type == "keyword" {
		m.Method = "GET"
	}
	if m.Interval == 0 {
		m.Interval = 300
	}
	m.Interval = clamp(m.Interval, 30, 86400)
	if m.Timeout == 0 {
		m.Timeout = 30
	}
	m.Timeout = clamp(m.Timeout, 1, 120)
	if m.Retries == 0 {
		m.Retries = 2
	}
	m.Retries = clamp(m.Retries, 1, 10)
	if strings.TrimSpace(m.Expect) == "" {
		m.Expect = "200-399"
	}
	return nil
}

func clamp(n, lo, hi int) int {
	if n < lo {
		return lo
	}
	if n > hi {
		return hi
	}
	return n
}

func (s *Server) doCheck(ctx context.Context, m Monitor) (Check, int64) {
	t0 := time.Now()
	c := Check{T: t0.UnixMilli()}
	timeout := time.Duration(m.Timeout) * time.Second

	if m.Type == "tcp" {
		d := net.Dialer{Timeout: timeout}
		conn, err := d.DialContext(ctx, "tcp", m.URL)
		c.Ms = int(time.Since(t0).Milliseconds())
		if err != nil {
			c.Err = shortErr(err)
			return c, 0
		}
		conn.Close()
		c.Up = true
		return c, 0
	}

	cctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()
	req, err := http.NewRequestWithContext(cctx, m.Method, m.URL, nil)
	if err != nil {
		c.Err = shortErr(err)
		return c, 0
	}
	req.Header.Set("User-Agent", "Uptimer/1.0")
	resp, err := s.client.Do(req)
	if err != nil {
		c.Ms = int(time.Since(t0).Milliseconds())
		c.Err = shortErr(err)
		return c, 0
	}
	defer resp.Body.Close()
	c.Code = resp.StatusCode
	var cert int64
	if resp.TLS != nil && len(resp.TLS.PeerCertificates) > 0 {
		cert = resp.TLS.PeerCertificates[0].NotAfter.UnixMilli()
	}
	var body []byte
	if m.Type == "keyword" {
		body, _ = io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	} else {
		io.Copy(io.Discard, io.LimitReader(resp.Body, 1<<16))
	}
	c.Ms = int(time.Since(t0).Milliseconds())
	switch {
	case !parseExpect(m.Expect)(resp.StatusCode):
		c.Err = fmt.Sprintf("HTTP %d", resp.StatusCode)
	case m.Type == "keyword" && !strings.Contains(string(body), m.Keyword):
		c.Err = "không thấy từ khoá"
	default:
		c.Up = true
	}
	return c, cert
}

func (s *Server) record(id string, c Check, cert int64) {
	var ev, msg string
	var mon Monitor

	s.mu.Lock()
	st := s.mons[id]
	if st == nil || st.Paused {
		s.mu.Unlock()
		return
	}
	st.Checks = append(st.Checks, c)
	if len(st.Checks) > maxChecks {
		st.Checks = append([]Check(nil), st.Checks[len(st.Checks)-maxChecks:]...)
	}
	day := time.UnixMilli(c.T).UTC().Format("2006-01-02")
	d := st.Days[day]
	if d == nil {
		d = &Day{}
		st.Days[day] = d
	}
	d.N++
	if c.Up {
		d.Up++
		d.Ms += c.Ms
		d.MsN++
	}
	if len(st.Days) > keepDays+10 {
		cutoff := time.Now().UTC().AddDate(0, 0, -keepDays).Format("2006-01-02")
		for k := range st.Days {
			if k < cutoff {
				delete(st.Days, k)
			}
		}
	}
	if cert > 0 {
		st.CertExpiry = cert
	}

	if c.Up {
		if st.Status == "down" {
			var downFor time.Duration
			if n := len(st.Incidents); n > 0 && st.Incidents[n-1].End == 0 {
				st.Incidents[n-1].End = c.T
				downFor = time.Duration(c.T-st.Incidents[n-1].Start) * time.Millisecond
			}
			ev = "up"
			msg = fmt.Sprintf("🟢 %s đã hoạt động trở lại (down %s)", st.Name, fmtDur(downFor))
		}
		if st.Status != "up" {
			st.Since = c.T
		}
		st.Status = "up"
		st.fails = 0
	} else {
		if st.fails == 0 {
			st.failStart = c.T
			st.failReason = c.Err
		}
		st.fails++
		if st.fails >= st.Retries && st.Status != "down" {
			st.Status = "down"
			st.Since = st.failStart
			st.Incidents = append(st.Incidents, Incident{Start: st.failStart, Reason: c.Err})
			if len(st.Incidents) > maxIncidents {
				st.Incidents = st.Incidents[len(st.Incidents)-maxIncidents:]
			}
			ev = "down"
			msg = fmt.Sprintf("🔴 %s đang DOWN — %s", st.Name, c.Err)
		}
	}
	mon = st.Monitor
	s.dirty = true
	s.mu.Unlock()

	if ev != "" {
		go s.notify(ev, mon, msg)
	}
}

func (s *Server) notify(ev string, m Monitor, text string) {
	s.mu.RLock()
	cfg := s.set
	s.mu.RUnlock()

	postJSON := func(label, u string, body any) {
		b, _ := json.Marshal(body)
		req, err := http.NewRequest("POST", u, bytes.NewReader(b))
		if err != nil {
			log.Printf("cảnh báo %s: URL không hợp lệ", label)
			return
		}
		req.Header.Set("Content-Type", "application/json")
		resp, err := notifyClient.Do(req)
		if err != nil {
			log.Printf("cảnh báo %s thất bại: %s", label, shortErr(err))
			return
		}
		resp.Body.Close()
		if resp.StatusCode >= 300 {
			log.Printf("cảnh báo %s: HTTP %d", label, resp.StatusCode)
		}
	}
	if cfg.Webhook != "" {
		postJSON("webhook", cfg.Webhook, map[string]any{
			"event": ev, "monitor": m.Name, "url": m.URL, "message": text,
			"time": time.Now().Format(time.RFC3339),
		})
	}
	if cfg.Discord != "" {
		postJSON("discord", cfg.Discord, map[string]string{"content": text + "\n" + m.URL})
	}
	if cfg.TgToken != "" && cfg.TgChat != "" {
		resp, err := notifyClient.PostForm("https://api.telegram.org/bot"+cfg.TgToken+"/sendMessage",
			url.Values{"chat_id": {cfg.TgChat}, "text": {text + "\n" + m.URL}})
		if err != nil {
			log.Printf("cảnh báo telegram thất bại: %s", shortErr(err))
		} else {
			resp.Body.Close()
			if resp.StatusCode >= 300 {
				log.Printf("cảnh báo telegram: HTTP %d", resp.StatusCode)
			}
		}
	}
}

func (s *Server) startLocked(st *State) {
	if c, ok := s.cancels[st.ID]; ok {
		c()
		delete(s.cancels, st.ID)
	}
	if st.Paused {
		return
	}
	ctx, cancel := context.WithCancel(context.Background())
	s.cancels[st.ID] = cancel
	go s.loop(ctx, st.ID)
}

func (s *Server) loop(ctx context.Context, id string) {
	select {
	case <-ctx.Done():
		return
	case <-time.After(time.Duration(mrand.Intn(2000)) * time.Millisecond):
	}
	for {
		s.mu.RLock()
		st := s.mons[id]
		var m Monitor
		if st != nil {
			m = st.Monitor
		}
		s.mu.RUnlock()
		if st == nil {
			return
		}
		c, cert := s.doCheck(ctx, m)
		if ctx.Err() != nil {
			return
		}
		s.record(id, c, cert)
		select {
		case <-ctx.Done():
			return
		case <-time.After(time.Duration(m.Interval) * time.Second):
		}
	}
}

type SparkPt struct {
	Ms int  `json:"ms"`
	Up bool `json:"up"`
}

type SeriesPt struct {
	T  int64 `json:"t"`
	Ms int   `json:"ms"`
	Up bool  `json:"up"`
}

type DayView struct {
	Date string  `json:"date"`
	Pct  float64 `json:"pct"`
}

type View struct {
	Monitor
	Status     string     `json:"status"`
	Since      int64      `json:"since"`
	CertExpiry int64      `json:"certExpiry"`
	Last       *Check     `json:"last,omitempty"`
	Up24       float64    `json:"up24"`
	Up7        float64    `json:"up7"`
	Up30       float64    `json:"up30"`
	AvgMs      int        `json:"avgMs"`
	Spark      []SparkPt  `json:"spark"`
	Days       []DayView  `json:"days"`
	Incidents  []Incident `json:"incidents"`
	Series     []SeriesPt `json:"series,omitempty"`
}

func statusOf(st *State) string {
	if st.Paused {
		return "paused"
	}
	return st.Status
}

func (st *State) uptimeDays(n int) float64 {
	now := time.Now().UTC()
	var total, up int
	for i := 0; i < n; i++ {
		if d := st.Days[now.AddDate(0, 0, -i).Format("2006-01-02")]; d != nil {
			total += d.N
			up += d.Up
		}
	}
	if total == 0 {
		return -1
	}
	return float64(up) / float64(total) * 100
}

func (st *State) uptime24() (float64, int) {
	cutoff := nowMs() - 86400000
	var total, up, msSum int
	for i := len(st.Checks) - 1; i >= 0; i-- {
		c := st.Checks[i]
		if c.T < cutoff {
			break
		}
		total++
		if c.Up {
			up++
			msSum += c.Ms
		}
	}
	if total == 0 {
		return -1, 0
	}
	avg := 0
	if up > 0 {
		avg = msSum / up
	}
	return float64(up) / float64(total) * 100, avg
}

func series(checks []Check, since int64, maxPts int) []SeriesPt {
	var cs []Check
	for _, c := range checks {
		if c.T >= since {
			cs = append(cs, c)
		}
	}
	if len(cs) == 0 {
		return nil
	}
	step := (len(cs) + maxPts - 1) / maxPts
	var out []SeriesPt
	for i := 0; i < len(cs); i += step {
		j := min(i+step, len(cs))
		up, sum, n := true, 0, 0
		for _, c := range cs[i:j] {
			if !c.Up {
				up = false
			} else {
				sum += c.Ms
				n++
			}
		}
		ms := 0
		if n > 0 {
			ms = sum / n
		}
		out = append(out, SeriesPt{T: cs[i].T, Ms: ms, Up: up})
	}
	return out
}

func dayViews(st *State, n int) []DayView {
	now := time.Now().UTC()
	out := make([]DayView, 0, n)
	for i := n - 1; i >= 0; i-- {
		key := now.AddDate(0, 0, -i).Format("2006-01-02")
		pct := -1.0
		if d := st.Days[key]; d != nil && d.N > 0 {
			pct = float64(d.Up) / float64(d.N) * 100
		}
		out = append(out, DayView{Date: key, Pct: pct})
	}
	return out
}

func view(st *State, detail bool) View {
	v := View{Monitor: st.Monitor, Status: statusOf(st), Since: st.Since, CertExpiry: st.CertExpiry}
	if n := len(st.Checks); n > 0 {
		c := st.Checks[n-1]
		v.Last = &c
	}
	v.Up24, v.AvgMs = st.uptime24()
	v.Up7 = st.uptimeDays(7)
	v.Up30 = st.uptimeDays(30)
	from := len(st.Checks) - 60
	if from < 0 {
		from = 0
	}
	for _, c := range st.Checks[from:] {
		v.Spark = append(v.Spark, SparkPt{Ms: c.Ms, Up: c.Up})
	}
	v.Days = dayViews(st, 30)
	inc := st.Incidents
	if !detail && len(inc) > 5 {
		inc = inc[len(inc)-5:]
	}
	v.Incidents = make([]Incident, 0, len(inc))
	for i := len(inc) - 1; i >= 0; i-- {
		v.Incidents = append(v.Incidents, inc[i])
	}
	if detail {
		v.Series = series(st.Checks, nowMs()-86400000, 240)
	}
	return v
}

func (s *Server) sortedLocked() []*State {
	out := make([]*State, 0, len(s.mons))
	for _, st := range s.mons {
		out = append(out, st)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Created != out[j].Created {
			return out[i].Created < out[j].Created
		}
		return out[i].Name < out[j].Name
	})
	return out
}

func (s *Server) save() error {
	s.mu.Lock()
	ds := diskState{Settings: s.set, Pass: s.pass}
	for _, st := range s.sortedLocked() {
		ds.Monitors = append(ds.Monitors, st)
	}
	b, err := json.Marshal(ds)
	s.dirty = false
	s.mu.Unlock()
	if err != nil {
		return err
	}
	tmp := s.file + ".tmp"
	if err := os.WriteFile(tmp, b, 0o600); err != nil {
		return err
	}
	return os.Rename(tmp, s.file)
}

func (s *Server) load() {
	b, err := os.ReadFile(s.file)
	if err != nil {
		return
	}
	var ds diskState
	if err := json.Unmarshal(b, &ds); err != nil {
		log.Printf("không đọc được %s: %v", s.file, err)
		return
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	s.set = ds.Settings
	if ds.Pass != "" {
		s.pass = ds.Pass
	}
	for _, st := range ds.Monitors {
		if st.ID == "" {
			continue
		}
		if st.Days == nil {
			st.Days = map[string]*Day{}
		}
		if st.Status == "" {
			st.Status = "pending"
		}
		s.mons[st.ID] = st
		s.startLocked(st)
	}
}

func writeJSON(w http.ResponseWriter, code int, v any) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(code)
	json.NewEncoder(w).Encode(v)
}

func jerr(w http.ResponseWriter, code int, msg string) {
	writeJSON(w, code, map[string]string{"error": msg})
}

func readJSON(w http.ResponseWriter, r *http.Request, v any) error {
	return json.NewDecoder(http.MaxBytesReader(w, r.Body, 1<<20)).Decode(v)
}

func (s *Server) auth(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/login" || r.URL.Path == "/logout" {
			next(w, r)
			return
		}
		if s.pass == "" {
			next(w, r)
			return
		}
		c, err := r.Cookie("uptimer_session")
		if err != nil || c.Value == "" {
			if strings.HasPrefix(r.URL.Path, "/api/") {
				jerr(w, 401, "chưa đăng nhập")
				return
			}
			http.Redirect(w, r, "/login", http.StatusFound)
			return
		}
		s.mu.RLock()
		_, ok := s.sessions[c.Value]
		s.mu.RUnlock()
		if !ok {
			if strings.HasPrefix(r.URL.Path, "/api/") {
				jerr(w, 401, "phiên đăng nhập hết hạn")
				return
			}
			http.SetCookie(w, &http.Cookie{Name: "uptimer_session", Value: "", Path: "/", MaxAge: -1})
			http.Redirect(w, r, "/login", http.StatusFound)
			return
		}
		next(w, r)
	}
}

func (s *Server) loginPage(w http.ResponseWriter, r *http.Request) {
	if c, err := r.Cookie("uptimer_session"); err == nil && c.Value != "" {
		s.mu.RLock()
		_, ok := s.sessions[c.Value]
		s.mu.RUnlock()
		if ok {
			http.Redirect(w, r, "/", http.StatusFound)
			return
		}
	}

	if r.Method == http.MethodPost {
		if err := r.ParseForm(); err != nil {
			http.Error(w, "Lỗi form", 400)
			return
		}
		user := strings.TrimSpace(r.FormValue("user"))
		pass := r.FormValue("pass")
		s.mu.RLock()
		ok := subtle.ConstantTimeCompare([]byte(user), []byte("admin")) == 1 &&
			subtle.ConstantTimeCompare([]byte(pass), []byte(s.pass)) == 1
		s.mu.RUnlock()
		if !ok {
			w.Header().Set("Content-Type", "text/html; charset=utf-8")
			io.WriteString(w, loginHTML("Sai tên đăng nhập hoặc mật khẩu"))
			return
		}
		b := make([]byte, 16)
		if _, err := rand.Read(b); err != nil {
			http.Error(w, "Lỗi hệ thống", 500)
			return
		}
		token := hex.EncodeToString(b)
		s.mu.Lock()
		s.sessions[token] = struct{}{}
		s.mu.Unlock()
		http.SetCookie(w, &http.Cookie{
			Name:     "uptimer_session",
			Value:    token,
			Path:     "/",
			HttpOnly: true,
			MaxAge:   7 * 24 * 3600,
			SameSite: http.SameSiteLaxMode,
		})
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	io.WriteString(w, loginHTML(""))
}

func (s *Server) logout(w http.ResponseWriter, r *http.Request) {
	c, err := r.Cookie("uptimer_session")
	if err == nil && c.Value != "" {
		s.mu.Lock()
		delete(s.sessions, c.Value)
		s.mu.Unlock()
	}
	http.SetCookie(w, &http.Cookie{
		Name:     "uptimer_session",
		Value:    "",
		Path:     "/",
		HttpOnly: true,
		MaxAge:   -1,
	})
	http.Redirect(w, r, "/login", http.StatusFound)
}

func (s *Server) api(w http.ResponseWriter, r *http.Request) {
	parts := strings.Split(strings.Trim(strings.TrimPrefix(r.URL.Path, "/api/"), "/"), "/")
	switch parts[0] {
	case "monitors":
		switch {
		case len(parts) == 1 && r.Method == http.MethodGet:
			s.mu.RLock()
			vs := make([]View, 0, len(s.mons))
			for _, st := range s.sortedLocked() {
				vs = append(vs, view(st, false))
			}
			s.mu.RUnlock()
			writeJSON(w, 200, vs)
		case len(parts) == 1 && r.Method == http.MethodPost:
			s.createMonitor(w, r)
		case len(parts) == 2:
			s.monitorByID(w, r, parts[1])
		case len(parts) == 3 && r.Method == http.MethodPost:
			s.monitorAction(w, r, parts[1], parts[2])
		default:
			jerr(w, 404, "không tìm thấy")
		}
	case "settings":
		switch r.Method {
		case http.MethodGet:
			s.mu.RLock()
			cfg := s.set
			s.mu.RUnlock()
			writeJSON(w, 200, cfg)
		case http.MethodPut:
			var in struct {
				Settings
				NewPassword     string `json:"newPassword"`
				ConfirmPassword string `json:"confirmPassword"`
			}
			if err := readJSON(w, r, &in); err != nil {
				jerr(w, 400, "JSON không hợp lệ")
				return
			}
			if in.NewPassword != "" {
				if in.NewPassword != in.ConfirmPassword {
					jerr(w, 400, "mật khẩu mới và xác nhận không khớp")
					return
				}
				if len(in.NewPassword) < 4 {
					jerr(w, 400, "mật khẩu mới quá ngắn (tối thiểu 4 ký tự)")
					return
				}
			}
			s.mu.Lock()
			s.set = in.Settings
			if in.NewPassword != "" {
				s.pass = in.NewPassword
				s.sessions = map[string]struct{}{}
			}
			s.dirty = true
			s.mu.Unlock()
			writeJSON(w, 200, map[string]bool{"ok": true})
		default:
			jerr(w, 405, "phương thức không hỗ trợ")
		}
	case "test-alert":
		if r.Method != http.MethodPost {
			jerr(w, 405, "chỉ hỗ trợ POST")
			return
		}
		go s.notify("test", Monitor{Name: "Thử cảnh báo", URL: "https://example.com"}, "✅ Uptimer: tin nhắn thử cảnh báo")
		writeJSON(w, 200, map[string]bool{"ok": true})
	default:
		jerr(w, 404, "không tìm thấy")
	}
}

func (s *Server) createMonitor(w http.ResponseWriter, r *http.Request) {
	var m Monitor
	if err := readJSON(w, r, &m); err != nil {
		jerr(w, 400, "JSON không hợp lệ")
		return
	}
	if err := normalize(&m); err != nil {
		jerr(w, 400, err.Error())
		return
	}
	m.ID = newID()
	m.Created = nowMs()
	m.Paused = false
	st := &State{Monitor: m, Status: "pending", Days: map[string]*Day{}}
	s.mu.Lock()
	s.mons[m.ID] = st
	s.startLocked(st)
	s.dirty = true
	s.mu.Unlock()
	writeJSON(w, 201, map[string]string{"id": m.ID})
}

func (s *Server) monitorByID(w http.ResponseWriter, r *http.Request, id string) {
	switch r.Method {
	case http.MethodGet:
		s.mu.RLock()
		st := s.mons[id]
		var v View
		if st != nil {
			v = view(st, true)
		}
		s.mu.RUnlock()
		if st == nil {
			jerr(w, 404, "không có monitor này")
			return
		}
		writeJSON(w, 200, v)
	case http.MethodPut:
		var in Monitor
		if err := readJSON(w, r, &in); err != nil {
			jerr(w, 400, "JSON không hợp lệ")
			return
		}
		if err := normalize(&in); err != nil {
			jerr(w, 400, err.Error())
			return
		}
		s.mu.Lock()
		st := s.mons[id]
		if st == nil {
			s.mu.Unlock()
			jerr(w, 404, "không có monitor này")
			return
		}
		in.ID, in.Created, in.Paused = st.ID, st.Created, st.Paused
		st.Monitor = in
		st.fails = 0
		s.startLocked(st)
		s.dirty = true
		s.mu.Unlock()
		writeJSON(w, 200, map[string]bool{"ok": true})
	case http.MethodDelete:
		s.mu.Lock()
		if c, ok := s.cancels[id]; ok {
			c()
			delete(s.cancels, id)
		}
		_, existed := s.mons[id]
		delete(s.mons, id)
		s.dirty = true
		s.mu.Unlock()
		if !existed {
			jerr(w, 404, "không có monitor này")
			return
		}
		writeJSON(w, 200, map[string]bool{"ok": true})
	default:
		jerr(w, 405, "phương thức không hỗ trợ")
	}
}

func (s *Server) monitorAction(w http.ResponseWriter, r *http.Request, id, action string) {
	switch action {
	case "pause":
		s.mu.Lock()
		st := s.mons[id]
		if st != nil {
			st.Paused = true
			s.startLocked(st)
			s.dirty = true
		}
		s.mu.Unlock()
		if st == nil {
			jerr(w, 404, "không có monitor này")
			return
		}
	case "resume":
		s.mu.Lock()
		st := s.mons[id]
		if st != nil {
			st.Paused = false
			st.Status = "pending"
			st.fails = 0
			s.startLocked(st)
			s.dirty = true
		}
		s.mu.Unlock()
		if st == nil {
			jerr(w, 404, "không có monitor này")
			return
		}
	case "check":
		s.mu.RLock()
		st := s.mons[id]
		var m Monitor
		if st != nil {
			m = st.Monitor
		}
		s.mu.RUnlock()
		if st == nil {
			jerr(w, 404, "không có monitor này")
			return
		}
		c, cert := s.doCheck(r.Context(), m)
		s.record(id, c, cert)
		writeJSON(w, 200, c)
		return
	default:
		jerr(w, 404, "hành động không hợp lệ")
		return
	}
	writeJSON(w, 200, map[string]bool{"ok": true})
}

func (s *Server) statusJSON(w http.ResponseWriter, r *http.Request) {
	type item struct {
		Name   string    `json:"name"`
		Status string    `json:"status"`
		Up30   float64   `json:"up30"`
		Since  int64     `json:"since"`
		Days   []DayView `json:"days"`
	}
	s.mu.RLock()
	title := s.set.Title
	if title == "" {
		title = "Trạng thái hệ thống"
	}
	items := make([]item, 0, len(s.mons))
	overall := "up"
	for _, st := range s.sortedLocked() {
		stt := statusOf(st)
		if stt == "paused" {
			continue
		}
		if stt == "down" {
			overall = "down"
		}
		items = append(items, item{Name: st.Name, Status: stt, Up30: st.uptimeDays(30), Since: st.Since, Days: dayViews(st, 30)})
	}
	s.mu.RUnlock()
	writeJSON(w, 200, map[string]any{"title": title, "overall": overall, "items": items, "time": nowMs()})
}

func page(html string) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/" && r.URL.Path != "/status" {
			http.NotFound(w, r)
			return
		}
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		io.WriteString(w, html)
	}
}

func defaultAddr() string {
	if p := os.Getenv("PORT"); p != "" {
		return ":" + p
	}
	return ":8288"
}

func main() {
	addr := flag.String("addr", defaultAddr(), "địa chỉ lắng nghe")
	data := flag.String("data", "uptimer-data.json", "file lưu dữ liệu")
	pass := flag.String("pass", os.Getenv("UPTIMER_PASS"), "mật khẩu admin (user: admin)")
	seed := flag.String("seed", os.Getenv("UPTIMER_SEED"), "URL tự thêm khi chưa có monitor nào, cách nhau bằng dấu phẩy")
	flag.Parse()

	s := &Server{
		mons:     map[string]*State{},
		cancels:  map[string]context.CancelFunc{},
		sessions: map[string]struct{}{},
		file:     *data,
		pass:     *pass,
		client: &http.Client{Transport: &http.Transport{
			DisableKeepAlives:   true,
			TLSHandshakeTimeout: 15 * time.Second,
			Proxy:               http.ProxyFromEnvironment,
		}},
	}
	s.load()

	if s.pass == "" {
		s.pass = "admin"
		s.dirty = true
		log.Println("Sử dụng mật khẩu mặc định: admin (nên đổi trên giao diện)")
	} else if s.pass == "admin" {
		log.Println("CẢNH BÁO: đang dùng mật khẩu mặc định 'admin', nên đổi ngay")
	}

	if strings.TrimSpace(*seed) != "" {
		s.mu.Lock()
		empty := len(s.mons) == 0
		s.mu.Unlock()
		if empty {
			for _, u := range strings.Split(*seed, ",") {
				m := Monitor{URL: strings.TrimSpace(u)}
				if m.URL == "" || normalize(&m) != nil {
					continue
				}
				if parsed, err := url.Parse(m.URL); err == nil {
					m.Name = parsed.Host
				}
				m.ID, m.Created = newID(), nowMs()
				st := &State{Monitor: m, Status: "pending", Days: map[string]*Day{}}
				s.mu.Lock()
				s.mons[m.ID] = st
				s.startLocked(st)
				s.dirty = true
				s.mu.Unlock()
			}
		}
	}

	mux := http.NewServeMux()
	mux.HandleFunc("/login", s.loginPage)
	mux.HandleFunc("/logout", s.logout)
	mux.HandleFunc("/", s.auth(page(dashboardHTML)))
	mux.HandleFunc("/api/", s.auth(s.api))
	mux.HandleFunc("/status", page(statusHTML))
	mux.HandleFunc("/status.json", s.statusJSON)
	mux.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, "ok") })

	ctx, stop := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer stop()
	srv := &http.Server{Addr: *addr, Handler: mux, ReadHeaderTimeout: 10 * time.Second}

	go func() {
		t := time.NewTicker(time.Minute)
		defer t.Stop()
		for {
			select {
			case <-ctx.Done():
				return
			case <-t.C:
				s.mu.RLock()
				d := s.dirty
				s.mu.RUnlock()
				if d {
					if err := s.save(); err != nil {
						log.Printf("lưu dữ liệu lỗi: %v", err)
					}
				}
			}
		}
	}()
	go func() {
		<-ctx.Done()
		sh, cancel := context.WithTimeout(context.Background(), 5*time.Second)
		defer cancel()
		srv.Shutdown(sh)
	}()

	log.Printf("Uptimer đang chạy tại http://localhost%s (dữ liệu: %s)", *addr, *data)
	if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
		log.Fatal(err)
	}
	if err := s.save(); err != nil {
		log.Printf("lưu dữ liệu lỗi: %v", err)
	}
}

// ---------- Giao diện ----------

func loginHTML(err string) string {
	errHTML := ""
	if err != "" {
		errHTML = `<div class="err">` + err + `</div>`
	}
	return `<!doctype html>
<html lang="vi"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Đăng nhập — Uptimer</title>
<style>
:root{--bg:#fafafa;--card:#fff;--border:#e5e7eb;--border-strong:#d1d5db;--fg:#09090b;--mut:#71717a;--accent:#4f46e5;--danger:#dc2626;--danger-bg:#fef2f2;--danger-bd:#fecaca;--sh:0 1px 2px rgba(0,0,0,.05)}
@media(prefers-color-scheme:dark){:root{--bg:#09090b;--card:#0c0c0f;--border:#27272a;--border-strong:#3f3f46;--fg:#fafafa;--mut:#a1a1aa;--accent:#818cf8;--danger:#ef4444;--danger-bg:rgba(239,68,68,.1);--danger-bd:rgba(239,68,68,.25);--sh:0 1px 2px rgba(0,0,0,.4)}}
*{box-sizing:border-box}
body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:var(--bg);color:var(--fg);font:14px/1.5 ui-sans-serif,system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;-webkit-font-smoothing:antialiased;font-feature-settings:"cv02","cv03","cv04","cv11";padding:24px}
.wrap{width:100%;max-width:360px}
.logo-wrap{display:flex;justify-content:center;margin-bottom:20px}
.logo{width:44px;height:44px;border-radius:10px;background:linear-gradient(135deg,#4f46e5,#7c3aed);display:flex;align-items:center;justify-content:center;font-size:20px;color:#fff;box-shadow:0 4px 12px rgba(79,70,229,.35)}
.card{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:28px;box-shadow:var(--sh)}
h1{margin:0 0 4px;font-size:17px;font-weight:600;letter-spacing:-0.015em;text-align:center}
.sub{margin:0 0 20px;color:var(--mut);font-size:12.5px;text-align:center}
label{display:block;font-size:12px;font-weight:500;margin-bottom:5px}
input{width:100%;height:36px;padding:0 11px;font:inherit;font-size:13px;border:1px solid var(--border);border-radius:6px;background:var(--bg);color:var(--fg);transition:border-color .12s,box-shadow .12s;margin-bottom:12px}
input:focus{outline:none;border-color:var(--border-strong);box-shadow:0 0 0 3px rgba(0,0,0,.04)}
@media(prefers-color-scheme:dark){input:focus{box-shadow:0 0 0 3px rgba(255,255,255,.06)}}
button{width:100%;height:36px;border:none;border-radius:6px;background:var(--fg);color:var(--card);font:inherit;font-size:13px;font-weight:500;cursor:pointer;transition:opacity .12s,transform .04s;margin-top:4px}
button:hover{opacity:.9}
button:active{transform:translateY(.5px)}
.err{background:var(--danger-bg);color:var(--danger);padding:9px 12px;border-radius:6px;font-size:12.5px;margin-bottom:14px;border:1px solid var(--danger-bd);text-align:center}
.hint{margin-top:16px;text-align:center;font-size:11px;color:var(--mut)}
kbd{display:inline-block;padding:1px 5px;border:1px solid var(--border);border-bottom-width:2px;border-radius:3px;font-family:ui-monospace,monospace;font-size:10px;background:var(--card);color:var(--fg)}
</style></head><body>
<div class="wrap">
<div class="logo-wrap"><div class="logo">📡</div></div>
<div class="card">
<h1>Đăng nhập</h1>
<p class="sub">Nhập thông tin để tiếp tục</p>
` + errHTML + `
<form method="POST" action="/login">
<label>Tên đăng nhập</label>
<input name="user" value="admin" autocomplete="username" required autofocus>
<label>Mật khẩu</label>
<input name="pass" type="password" autocomplete="current-password" placeholder="Mặc định: admin" required>
<button type="submit">Đăng nhập →</button>
</form>
<p class="hint">Giám sát uptime tự host · <kbd>admin</kbd> / <kbd>admin</kbd></p>
</div>
</div>
</body></html>`
}

const dashboardHTML = `<!doctype html>
<html lang="vi"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Uptimer</title>
<style>
:root{
  --bg:#fafafa;--bg-subtle:#f4f4f5;--card:#ffffff;
  --border:#e5e7eb;--border-strong:#d1d5db;
  --fg:#09090b;--mut:#71717a;--mut-subtle:#a1a1aa;
  --up:#059669;--up-bg:#ecfdf5;--up-bd:#a7f3d0;
  --down:#dc2626;--down-bg:#fef2f2;--down-bd:#fecaca;
  --warn:#d97706;--warn-bg:#fffbeb;--warn-bd:#fde68a;
  --pause:#71717a;--pause-bg:#f4f4f5;--pause-bd:#e5e7eb;
  --accent:#4f46e5;--focus:rgba(79,70,229,.2);
  --r:6px;--sh:0 1px 2px rgba(0,0,0,.05);--sh-md:0 4px 12px rgba(0,0,0,.08);
}
@media(prefers-color-scheme:dark){
  :root{
    --bg:#09090b;--bg-subtle:#18181b;--card:#0c0c0f;
    --border:#27272a;--border-strong:#3f3f46;
    --fg:#fafafa;--mut:#a1a1aa;--mut-subtle:#71717a;
    --up:#10b981;--up-bg:rgba(16,185,129,.1);--up-bd:rgba(16,185,129,.3);
    --down:#ef4444;--down-bg:rgba(239,68,68,.1);--down-bd:rgba(239,68,68,.3);
    --warn:#f59e0b;--warn-bg:rgba(245,158,11,.1);--warn-bd:rgba(245,158,11,.3);
    --pause:#71717a;--pause-bg:rgba(113,113,122,.15);--pause-bd:rgba(113,113,122,.3);
    --accent:#818cf8;--focus:rgba(129,140,248,.25);
    --sh:0 1px 2px rgba(0,0,0,.4);--sh-md:0 4px 12px rgba(0,0,0,.5);
  }
}
*{box-sizing:border-box}
html,body{margin:0;background:var(--bg);color:var(--fg);font:13.5px/1.5 ui-sans-serif,system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;-webkit-font-smoothing:antialiased;font-feature-settings:"cv02","cv03","cv04","cv11"}
a{color:inherit;text-decoration:none}
button{font:inherit}
kbd{display:inline-block;padding:1px 5px;border:1px solid var(--border);border-bottom-width:2px;border-radius:3px;font-family:ui-monospace,SFMono-Regular,monospace;font-size:10px;background:var(--card);color:var(--fg);line-height:1.4}

/* topbar */
.topbar{position:sticky;top:0;z-index:50;background:var(--card);border-bottom:1px solid var(--border);backdrop-filter:saturate(180%) blur(8px)}
.incident-banner{background:var(--down-bg);border-bottom:1px solid var(--down-bd);color:var(--down);padding:8px 20px;display:flex;align-items:center;gap:10px;font-size:12.5px;font-weight:500}
.incident-banner[hidden]{display:none}
.ib-ic{font-size:14px;flex:none}
.ib-text{flex:1}
.ib-text b{font-weight:700}
.ib-view{padding:3px 10px;border:1px solid var(--down-bd);background:transparent;color:var(--down);border-radius:4px;font-size:11.5px;font-weight:500;cursor:pointer}
.ib-view:hover{background:rgba(220,38,38,.08)}
.ib-close{background:transparent;border:none;color:var(--down);font-size:16px;cursor:pointer;padding:0 4px;opacity:.6}
.ib-close:hover{opacity:1}

.header-inner{max-width:1240px;margin:0 auto;padding:0 20px;height:52px;display:flex;align-items:center;gap:16px}
.brand{display:flex;align-items:center;gap:9px;font-weight:600;font-size:14px;letter-spacing:-0.01em;flex:none}
.brand-logo{width:26px;height:26px;border-radius:6px;background:linear-gradient(135deg,#4f46e5,#7c3aed);display:flex;align-items:center;justify-content:center;font-size:13px;color:#fff;box-shadow:0 1px 2px rgba(79,70,229,.4)}
.sync{width:6px;height:6px;border-radius:50%;background:var(--up);box-shadow:0 0 0 3px var(--up-bg);transition:all .2s;margin-left:2px}
.sync.syncing{background:var(--accent);box-shadow:0 0 0 3px var(--focus);animation:pulse 1s infinite}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.4}}
.nav{display:flex;gap:2px}
.nav a{padding:5px 10px;border-radius:5px;color:var(--mut);font-size:12.5px;font-weight:500;transition:background .1s,color .1s}
.nav a:hover{background:var(--bg-subtle);color:var(--fg)}
.nav a.active{color:var(--fg)}
.actions{margin-left:auto;display:flex;gap:6px;align-items:center}

/* buttons */
.btn{height:30px;padding:0 11px;font-size:12.5px;font-weight:500;border:1px solid var(--border);background:var(--card);color:var(--fg);border-radius:var(--r);cursor:pointer;display:inline-flex;align-items:center;gap:6px;transition:background .1s,border-color .1s,transform .04s;line-height:1;white-space:nowrap}
.btn:hover{background:var(--bg-subtle);border-color:var(--border-strong)}
.btn:active{transform:translateY(.5px)}
.btn:disabled{opacity:.4;cursor:not-allowed}
.btn-primary{background:var(--fg);color:var(--card);border-color:var(--fg)}
.btn-primary:hover{background:var(--fg);border-color:var(--fg);opacity:.88}
.btn-danger{color:var(--down)}
.btn-danger:hover{background:var(--down-bg);border-color:var(--down-bd)}
.btn-icon{padding:0;width:30px;justify-content:center;color:var(--mut)}
.btn-sm{height:26px;padding:0 9px;font-size:11.5px}
.btn-sm .k{color:var(--mut);font-size:10.5px;padding:0 3px;border:1px solid var(--border);border-radius:3px;line-height:1.3}

/* user menu */
.user-menu{position:relative}
.avatar{width:28px;height:28px;border-radius:50%;background:linear-gradient(135deg,#4f46e5,#7c3aed);color:#fff;font-weight:600;font-size:12px;border:none;cursor:pointer;display:flex;align-items:center;justify-content:center;letter-spacing:-0.02em}
.avatar:hover{opacity:.9}
.dropdown{position:absolute;top:calc(100% + 6px);right:0;background:var(--card);border:1px solid var(--border);border-radius:8px;box-shadow:var(--sh-md);min-width:200px;padding:4px;display:none;z-index:60;animation:pop .12s}
.dropdown.show{display:block}
.dropdown-header{padding:8px 10px 10px;border-bottom:1px solid var(--border);margin-bottom:4px}
.dropdown-header b{display:block;font-size:12.5px;font-weight:600}
.dropdown-header small{color:var(--mut);font-size:11px}
.dropdown button,.dropdown a{display:flex;width:100%;padding:6px 10px;background:transparent;border:none;text-align:left;font-size:12.5px;color:var(--fg);border-radius:4px;cursor:pointer;align-items:center;gap:8px;text-decoration:none}
.dropdown button:hover,.dropdown a:hover{background:var(--bg-subtle);text-decoration:none}
.dropdown hr{border:none;border-top:1px solid var(--border);margin:4px 0}
@keyframes pop{from{opacity:0;transform:translateY(-4px)}}

/* layout */
.main{max-width:1240px;margin:0 auto;padding:24px 20px}
.page-title{font-size:20px;font-weight:600;margin:0 0 2px;letter-spacing:-0.02em}
.page-sub{color:var(--mut);font-size:12.5px;margin:0 0 18px}

/* summary */
.summary{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:1px;background:var(--border);border:1px solid var(--border);border-radius:8px;overflow:hidden;margin-bottom:16px;box-shadow:var(--sh)}
.summary-item{background:var(--card);padding:12px 16px;min-width:0}
.summary-label{font-size:10.5px;font-weight:500;color:var(--mut);text-transform:uppercase;letter-spacing:0.06em;margin-bottom:3px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.summary-value{font-size:20px;font-weight:600;letter-spacing:-0.02em;line-height:1.15;font-variant-numeric:tabular-nums}
.summary-value.up{color:var(--up)}
.summary-value.down{color:var(--down)}
.summary-value.muted{color:var(--mut-subtle)}

/* toolbar */
.toolbar{display:flex;gap:8px;margin-bottom:10px;align-items:center;flex-wrap:wrap}
.search{flex:1;min-width:180px;position:relative}
.search input{width:100%;height:30px;padding:0 10px 0 30px;font-size:12.5px;border:1px solid var(--border);border-radius:var(--r);background:var(--card);color:var(--fg);transition:border-color .12s,box-shadow .12s}
.search input:focus{outline:none;border-color:var(--border-strong);box-shadow:0 0 0 3px var(--focus)}
.search::before{content:"🔍";position:absolute;left:9px;top:50%;transform:translateY(-50%);font-size:11px;opacity:.4;pointer-events:none}
.search kbd{position:absolute;right:6px;top:50%;transform:translateY(-50%);pointer-events:none;opacity:.5}
.search input:not(:placeholder-shown)~kbd{display:none}
.filters{display:flex;gap:1px;padding:2px;background:var(--bg-subtle);border-radius:var(--r);border:1px solid var(--border)}
.filters button{height:24px;padding:0 9px;font-size:11.5px;font-weight:500;border:none;background:transparent;color:var(--mut);border-radius:4px;cursor:pointer;transition:background .1s,color .1s;line-height:1}
.filters button:hover{color:var(--fg)}
.filters button.active{background:var(--card);color:var(--fg);box-shadow:0 1px 2px rgba(0,0,0,.06)}
.sort{height:30px;padding:0 8px;font-size:12.5px;border:1px solid var(--border);border-radius:var(--r);background:var(--card);color:var(--fg);cursor:pointer}
.sort:focus{outline:none;border-color:var(--border-strong);box-shadow:0 0 0 3px var(--focus)}

/* monitor */
.monitor{background:var(--card);border:1px solid var(--border);border-radius:8px;margin-bottom:8px;transition:border-color .12s,box-shadow .12s;overflow:hidden;position:relative}
.monitor:hover{border-color:var(--border-strong);box-shadow:var(--sh)}
.monitor.selected{border-color:var(--accent);box-shadow:0 0 0 2px var(--focus)}
.monitor[data-status="down"]{border-color:var(--down-bd)}
.monitor-head{padding:14px 16px 6px;display:flex;gap:10px;align-items:flex-start}
.cb{width:14px;height:14px;margin:5px 2px 0 0;cursor:pointer;accent-color:var(--accent);flex:none}
.status-dot{width:8px;height:8px;border-radius:50%;flex:none;margin-top:6px;position:relative}
.status-dot::after{content:"";position:absolute;inset:-3px;border-radius:50%;background:currentColor;opacity:.2}
.status-dot.up{background:var(--up);color:var(--up)}
.status-dot.down{background:var(--down);color:var(--down);animation:pulse 1.5s infinite}
.status-dot.pending{background:var(--warn);color:var(--warn);animation:pulse 2s infinite}
.status-dot.paused{background:var(--pause);color:var(--pause)}
.monitor-info{flex:1;min-width:0}
.monitor-name{font-size:13.5px;font-weight:600;margin:0;letter-spacing:-0.01em;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;line-height:1.35}
.monitor-url{font-size:11.5px;color:var(--mut);font-family:ui-monospace,SFMono-Regular,monospace;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;display:block;margin-top:1px}
.badge{display:inline-flex;align-items:center;gap:4px;padding:2px 8px;border-radius:4px;font-size:10.5px;font-weight:600;border:1px solid;letter-spacing:0.02em;white-space:nowrap;flex:none;line-height:1.4}
.badge::before{content:"";width:4px;height:4px;border-radius:50%;background:currentColor}
.badge.up{color:var(--up);background:var(--up-bg);border-color:var(--up-bd)}
.badge.down{color:var(--down);background:var(--down-bg);border-color:var(--down-bd)}
.badge.pending{color:var(--warn);background:var(--warn-bg);border-color:var(--warn-bd)}
.badge.paused{color:var(--pause);background:var(--pause-bg);border-color:var(--pause-bd)}

.monitor-body{padding:0 16px 10px}
.metrics{display:grid;grid-template-columns:repeat(auto-fit,minmax(85px,1fr));gap:12px;padding:8px 0 6px;border-top:1px solid var(--border);margin-top:4px}
.metric-label{font-size:10px;font-weight:500;color:var(--mut);text-transform:uppercase;letter-spacing:0.05em;margin-bottom:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.metric-value{font-size:13px;font-weight:600;font-variant-numeric:tabular-nums;letter-spacing:-0.01em;line-height:1.2}
.metric-value.warn{color:var(--warn)}
.metric-value.danger{color:var(--down)}
.metric-value.muted{color:var(--mut);font-weight:500}

.sparkline{margin-top:4px;height:32px;position:relative;color:var(--accent)}
.sparkline svg{display:block;width:100%;height:100%;overflow:visible}
.chart-empty{display:flex;align-items:center;justify-content:center;color:var(--mut-subtle);font-size:11px;height:100%}
.day-bars{display:flex;gap:2px;height:22px;margin-top:5px}
.day-bars i{flex:1;border-radius:2px;transition:transform .12s,opacity .12s;cursor:default;min-width:0}
.day-bars i:hover{transform:scaleY(1.15);opacity:.85}

.monitor-foot{padding:10px 16px;border-top:1px solid var(--border);display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap;background:var(--bg-subtle)}
.monitor-meta{display:flex;gap:14px;font-size:11px;color:var(--mut);flex-wrap:wrap;min-width:0}
.monitor-meta span{display:flex;align-items:center;gap:3px;white-space:nowrap}
.monitor-meta b{color:var(--fg);font-weight:500}
.monitor-actions{display:flex;gap:3px;flex-wrap:wrap}

/* detail */
.detail{padding:14px 16px;border-top:1px solid var(--border);background:var(--bg-subtle);animation:fade .12s}
@keyframes fade{from{opacity:0}}
.detail-section{margin-bottom:16px}
.detail-section:last-child{margin-bottom:0}
.detail-title{font-size:10px;font-weight:600;color:var(--mut);text-transform:uppercase;letter-spacing:0.06em;margin-bottom:6px}
.detail .sparkline{height:70px;background:var(--card);padding:6px;border-radius:5px;border:1px solid var(--border);margin-top:0}
.incidents-table{width:100%;border-collapse:collapse;font-size:11.5px;background:var(--card);border-radius:5px;overflow:hidden;border:1px solid var(--border)}
.incidents-table th{text-align:left;padding:6px 10px;background:var(--bg-subtle);font-weight:600;color:var(--mut);font-size:10px;text-transform:uppercase;letter-spacing:0.05em;border-bottom:1px solid var(--border)}
.incidents-table td{padding:6px 10px;border-bottom:1px solid var(--border);vertical-align:top}
.incidents-table tr:last-child td{border-bottom:none}
.incidents-table td:first-child{white-space:nowrap;color:var(--mut);font-variant-numeric:tabular-nums}

/* empty */
.empty{text-align:center;padding:44px 24px;color:var(--mut);background:var(--card);border:1px dashed var(--border);border-radius:8px}
.empty-icon{font-size:32px;margin-bottom:10px;opacity:.4}
.empty h3{font-size:14px;font-weight:600;color:var(--fg);margin:0 0 5px}
.empty p{margin:0;font-size:12.5px;line-height:1.5}
.no-match{margin-bottom:10px}

/* footer */
.footer{border-top:1px solid var(--border);background:var(--card);margin-top:28px;padding:10px 20px}
.footer-inner{max-width:1240px;margin:0 auto;display:flex;justify-content:space-between;gap:8px;flex-wrap:wrap;color:var(--mut);font-size:11px;align-items:center}
.kbd-hints{display:flex;gap:12px;flex-wrap:wrap}
.kbd-hints span{display:inline-flex;align-items:center;gap:4px}
.kbd-hints kbd{opacity:.8}

/* spinner */
.spinner{display:inline-block;width:11px;height:11px;border:1.5px solid var(--mut);border-top-color:transparent;border-radius:50%;animation:spin .7s linear infinite;vertical-align:middle;opacity:.6}
@keyframes spin{to{transform:rotate(360deg)}}

/* modals */
.modal{display:none;position:fixed;inset:0;background:rgba(0,0,0,.5);backdrop-filter:blur(3px);z-index:100;align-items:center;justify-content:center;padding:20px;animation:fade .12s}
.modal.show{display:flex}
.modal-box{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:22px;width:100%;max-width:540px;max-height:90vh;overflow-y:auto;box-shadow:0 24px 48px rgba(0,0,0,.22);animation:popin .15s}
.modal-box.sm{max-width:400px}
@keyframes popin{from{transform:scale(.97);opacity:0}}
.modal-title{font-size:16px;font-weight:600;margin:0 0 3px;letter-spacing:-0.01em}
.modal-sub{color:var(--mut);font-size:12.5px;margin:0 0 16px}
.field{margin-top:12px}
.field label{display:block;font-size:11.5px;font-weight:500;margin-bottom:5px;color:var(--fg)}
.field label small{color:var(--mut);font-weight:400;margin-left:2px}
.field input,.field select{width:100%;height:32px;padding:0 10px;font-size:12.5px;border:1px solid var(--border);border-radius:5px;background:var(--bg);color:var(--fg);transition:border-color .12s,box-shadow .12s}
.field input:focus,.field select:focus{outline:none;border-color:var(--border-strong);box-shadow:0 0 0 3px var(--focus)}
.field-hint{display:block;color:var(--mut);font-size:11px;margin-top:3px}
.row{display:grid;grid-template-columns:1fr 1fr;gap:10px}
@media(max-width:480px){.row{grid-template-columns:1fr}}
.section-title{font-size:10.5px;font-weight:600;text-transform:uppercase;letter-spacing:0.06em;color:var(--mut);margin:20px 0 0;padding-top:14px;border-top:1px solid var(--border)}
.modal-foot{display:flex;gap:6px;justify-content:flex-end;margin-top:20px;padding-top:14px;border-top:1px solid var(--border);flex-wrap:wrap}
.err-msg{background:var(--down-bg);color:var(--down);padding:7px 10px;border-radius:5px;font-size:11.5px;margin-top:10px;display:none;border:1px solid var(--down-bd)}
.err-msg.show{display:block}

/* command palette */
.cmd-box{max-width:520px;padding:0;overflow:hidden;display:flex;flex-direction:column;max-height:70vh}
.cmd-input{width:100%;height:44px;padding:0 18px;border:none;border-bottom:1px solid var(--border);background:transparent;color:var(--fg);font:inherit;font-size:13.5px;flex:none}
.cmd-input:focus{outline:none}
.cmd-input::placeholder{color:var(--mut-subtle)}
.cmd-list{overflow-y:auto;padding:6px;flex:1}
.cmd-group{font-size:10px;font-weight:600;color:var(--mut);text-transform:uppercase;letter-spacing:.06em;padding:6px 10px 4px}
.cmd-item{display:flex;align-items:center;gap:10px;padding:7px 10px;border-radius:5px;cursor:pointer;font-size:12.5px;color:var(--fg)}
.cmd-item:hover,.cmd-item.active{background:var(--bg-subtle)}
.cmd-item .k{margin-left:auto;color:var(--mut);font-size:11px;font-family:ui-monospace,monospace;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.cmd-empty{padding:28px 20px;text-align:center;color:var(--mut);font-size:12.5px}

/* help */
.help-table{width:100%;border-collapse:collapse;font-size:12.5px;margin-top:4px}
.help-table td{padding:7px 0;border-bottom:1px solid var(--border)}
.help-table tr:last-child td{border-bottom:none}
.help-table td:first-child{width:120px}

/* bulk bar */
.bulk{position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:var(--fg);color:var(--card);border-radius:8px;padding:8px 8px 8px 16px;display:flex;gap:10px;align-items:center;box-shadow:var(--sh-md);z-index:80;animation:slideup .18s}
.bulk[hidden]{display:none}
.bulk-count{font-size:12.5px;font-weight:500;white-space:nowrap}
.bulk-count b{font-weight:700}
.bulk-actions{display:flex;gap:2px}
.bulk-actions button{padding:5px 10px;background:rgba(255,255,255,.1);border:none;color:var(--card);border-radius:4px;font-size:11.5px;font-weight:500;cursor:pointer;transition:background .1s}
.bulk-actions button:hover{background:rgba(255,255,255,.2)}
.bulk-actions button.danger{color:#fca5a5}
.bulk-actions button.danger:hover{background:rgba(220,38,38,.3)}
.bulk-clear{background:transparent;border:none;color:var(--card);font-size:16px;cursor:pointer;padding:0 6px;opacity:.7}
.bulk-clear:hover{opacity:1}
@media(prefers-color-scheme:dark){.bulk{background:var(--card);color:var(--fg);border:1px solid var(--border)}.bulk-actions button{background:var(--bg-subtle);color:var(--fg)}.bulk-actions button:hover{background:var(--bg)}.bulk-actions button.danger{color:var(--down)}.bulk-clear{color:var(--fg)}}
@keyframes slideup{from{transform:translate(-50%,20px);opacity:0}}

/* toast */
#toasts{position:fixed;bottom:20px;right:20px;z-index:200;display:flex;flex-direction:column;gap:8px;max-width:340px}
.toast{background:var(--card);border:1px solid var(--border);border-radius:6px;padding:9px 12px;box-shadow:0 8px 24px rgba(0,0,0,.12);font-size:12.5px;animation:slidein .18s;display:flex;align-items:center;gap:9px;border-left:3px solid var(--fg)}
.toast.ok{border-left-color:var(--up)}
.toast.err{border-left-color:var(--down)}
.toast .ic{font-size:13px;flex:none}
@keyframes slidein{from{transform:translateX(20px);opacity:0}}

@media(prefers-reduced-motion:reduce){
  *,*::before,*::after{animation-duration:.01ms!important;animation-iteration-count:1!important;transition-duration:.01ms!important}
}

@media(max-width:640px){
  .header-inner{padding:0 14px;gap:10px}
  .nav{display:none}
  .main{padding:14px}
  .monitor-head{padding:12px 12px 4px}
  .monitor-body{padding:0 12px 8px}
  .monitor-foot{padding:8px 12px}
  .metrics{grid-template-columns:repeat(2,1fr);gap:10px}
  .monitor-actions .txt{display:none}
  .monitor-actions .btn-sm{padding:0 7px;width:26px;justify-content:center}
  .summary{grid-template-columns:repeat(2,1fr)}
  .footer-inner{flex-direction:column;align-items:flex-start;gap:6px}
  .kbd-hints{display:none}
}
</style></head><body>

<div class="topbar">
  <div class="incident-banner" id="incBanner" hidden>
    <span class="ib-ic">⚠</span>
    <span class="ib-text"><b id="ibCount">0</b> monitor đang gặp sự cố</span>
    <button class="ib-view" id="ibView">Xem</button>
    <button class="ib-close" id="ibClose" aria-label="Đóng">×</button>
  </div>
  <header>
  <div class="header-inner">
    <div class="brand"><span class="brand-logo">📡</span>Uptimer<span class="sync" id="sync" title="Đã đồng bộ"></span></div>
    <nav class="nav">
      <a href="/" class="active">Monitors</a>
      <a href="/status" target="_blank" rel="noopener noreferrer">Trang status</a>
    </nav>
    <div class="actions">
      <button class="btn btn-icon" id="cmdBtn" title="Lệnh (⌘K)">⌘K</button>
      <button class="btn btn-primary" id="add" title="Thêm (N)">+ Thêm</button>
      <div class="user-menu" id="userMenu">
        <button class="avatar" id="userBtn" aria-label="Menu người dùng">A</button>
        <div class="dropdown" id="userDrop">
          <div class="dropdown-header"><b>admin</b><small>Quản trị viên</small></div>
          <button data-mm="cfg">⚙ Cài đặt</button>
          <button type="button" data-mm="status">🌐 Trang status</button>
          <button data-mm="help">? Trợ giúp</button>
          <hr>
          <button data-mm="logout">↪ Đăng xuất</button>
        </div>
      </div>
    </div>
  </div>
  </header>
</div>

<main class="main">
<h1 class="page-title">Monitors</h1>
<p class="page-sub" id="sub">Tổng quan sức khoẻ hệ thống</p>

<div class="summary" id="sum"></div>

<div class="toolbar">
  <div class="search">
    <input type="search" id="q" placeholder="Tìm monitor..." autocomplete="off">
    <kbd>/</kbd>
  </div>
  <div class="filters" id="filters">
    <button data-f="all" class="active">Tất cả</button>
    <button data-f="up">Up</button>
    <button data-f="down">Down</button>
    <button data-f="paused">Dừng</button>
  </div>
  <select class="sort" id="sort" title="Sắp xếp">
    <option value="default">Mặc định</option>
    <option value="name">Tên A→Z</option>
    <option value="status">Trạng thái</option>
    <option value="uptime">Uptime thấp</option>
    <option value="latency">Phản hồi chậm</option>
  </select>
</div>

<div id="list"></div>
</main>

<footer class="footer">
<div class="footer-inner">
  <span id="upd">Đang tải…</span>
  <div class="kbd-hints">
    <span><kbd>N</kbd> thêm</span>
    <span><kbd>/</kbd> tìm</span>
    <span><kbd>⌘K</kbd> lệnh</span>
    <span><kbd>?</kbd> trợ giúp</span>
    <span><kbd>Esc</kbd> đóng</span>
  </div>
</div>
</footer>

<div class="bulk" id="bulk" hidden>
  <span class="bulk-count"><b id="bulkCount">0</b> đã chọn</span>
  <div class="bulk-actions">
    <button data-bulk="check">↻ Check</button>
    <button data-bulk="pause">⏸ Dừng</button>
    <button data-bulk="resume">▶ Tiếp</button>
    <button data-bulk="del" class="danger">🗑 Xoá</button>
  </div>
  <button class="bulk-clear" id="bulkClear" aria-label="Bỏ chọn">×</button>
</div>

<div class="modal" id="formModal">
<div class="modal-box">
<h3 class="modal-title" id="f_title">Thêm monitor</h3>
<p class="modal-sub">Cấu hình URL, chu kỳ kiểm tra và điều kiện thành công.</p>
<div class="field"><label>Tên hiển thị</label><input id="f_name" placeholder="Ví dụ: Website chính"></div>
<div class="row">
  <div class="field"><label>Loại</label>
    <select id="f_type">
      <option value="http">HTTP(S)</option>
      <option value="keyword">HTTP + từ khoá</option>
      <option value="tcp">TCP port</option>
    </select>
  </div>
  <div class="field"><label>Chu kỳ <small>(giây, ≥30)</small></label><input id="f_int" type="number" min="30" value="300"></div>
</div>
<div class="field"><label id="f_url_l">URL</label><input id="f_url" placeholder="https://example.com"></div>
<div class="field" id="f_kwbox"><label>Từ khoá phải xuất hiện</label><input id="f_kw" placeholder="Ví dụ: Welcome"></div>
<div class="row" id="f_httpbox">
  <div class="field"><label>Phương thức</label><select id="f_method"><option>GET</option><option>HEAD</option></select></div>
  <div class="field"><label>Mã HTTP hợp lệ</label><input id="f_exp" value="200-399"></div>
</div>
<div class="row">
  <div class="field"><label>Timeout <small>(giây)</small></label><input id="f_to" type="number" min="1" max="120" value="30"></div>
  <div class="field"><label>Thử lại trước DOWN</label><input id="f_ret" type="number" min="1" max="10" value="2"></div>
</div>
<div class="err-msg" id="f_err"></div>
<div class="modal-foot">
  <button class="btn" id="f_cancel">Huỷ</button>
  <button class="btn btn-primary" id="f_save">Lưu monitor</button>
</div>
</div>
</div>

<div class="modal" id="cfgModal">
<div class="modal-box">
<h3 class="modal-title">Cài đặt</h3>
<p class="modal-sub">Kênh cảnh báo và mật khẩu quản trị.</p>
<div class="field"><label>Tiêu đề trang status</label><input id="c_title" placeholder="Trạng thái hệ thống"></div>
<div class="section-title">Kênh cảnh báo</div>
<div class="field"><label>Webhook URL <small>(JSON POST)</small></label><input id="c_web" placeholder="https://..."><span class="field-hint">Nhận sự kiện UP/DOWN dạng JSON.</span></div>
<div class="field"><label>Discord webhook URL</label><input id="c_dis" placeholder="https://discord.com/api/webhooks/..."></div>
<div class="row">
  <div class="field"><label>Telegram bot token</label><input id="c_tgt" placeholder="123:ABC..."></div>
  <div class="field"><label>Telegram chat ID</label><input id="c_tgc" placeholder="-100..."></div>
</div>
<div class="section-title">Mật khẩu quản trị</div>
<div class="field"><label>Mật khẩu mới</label><input id="c_pass" type="password" placeholder="Để trống nếu không đổi" autocomplete="new-password"><span class="field-hint">Tối thiểu 4 ký tự. Đổi sẽ đăng xuất mọi phiên.</span></div>
<div class="field"><label>Xác nhận mật khẩu mới</label><input id="c_pass2" type="password" autocomplete="new-password"></div>
<div class="err-msg" id="c_err"></div>
<div class="modal-foot">
  <button class="btn" id="c_test">📨 Gửi thử</button>
  <button class="btn" id="c_close">Đóng</button>
  <button class="btn btn-primary" id="c_save">Lưu</button>
</div>
</div>
</div>

<div class="modal" id="confirmModal">
<div class="modal-box sm">
<h3 class="modal-title" id="cfTitle">Xác nhận</h3>
<p class="modal-sub" id="cfMsg" style="margin-bottom:16px"></p>
<div class="modal-foot" style="border-top:none;padding-top:0;margin-top:0">
  <button class="btn" id="cfCancel">Huỷ</button>
  <button class="btn btn-danger" id="cfOk" style="background:var(--down);color:#fff;border-color:var(--down)">Xác nhận</button>
</div>
</div>
</div>

<div class="modal" id="cmdModal">
<div class="modal-box cmd-box">
  <input class="cmd-input" id="cmdInput" placeholder="Gõ lệnh hoặc tên monitor..." autocomplete="off">
  <div class="cmd-list" id="cmdList"></div>
</div>
</div>

<div class="modal" id="helpModal">
<div class="modal-box">
<h3 class="modal-title">Phím tắt</h3>
<p class="modal-sub">Tăng tốc thao tác trên dashboard.</p>
<table class="help-table">
<tbody>
<tr><td><kbd>N</kbd></td><td>Thêm monitor mới</td></tr>
<tr><td><kbd>/</kbd></td><td>Tìm kiếm monitor</td></tr>
<tr><td><kbd>⌘K</kbd> / <kbd>Ctrl K</kbd></td><td>Mở command palette</td></tr>
<tr><td><kbd>?</kbd></td><td>Trợ giúp (trang này)</td></tr>
<tr><td><kbd>Esc</kbd></td><td>Đóng modal đang mở</td></tr>
<tr><td><kbd>Enter</kbd></td><td>Lưu form đang mở</td></tr>
<tr><td><kbd>↑</kbd> <kbd>↓</kbd></td><td>Di chuyển trong command palette</td></tr>
</tbody>
</table>
<div class="modal-foot"><button class="btn" id="helpClose">Đóng</button></div>
</div>
</div>

<div id="toasts"></div>

<script>
var $=function(id){return document.getElementById(id)};
function esc(s){return String(s==null?'':s).replace(/[&<>"']/g,function(c){return ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'})[c];});}
function api(method,path,body){
  var opt={method:method,headers:{}};
  if(body){opt.headers['Content-Type']='application/json';opt.body=JSON.stringify(body);}
  return fetch(path,opt).then(function(r){
    if(r.status===401){location.href='/login';throw new Error('Phiên đã hết hạn');}
    return r.json().then(function(j){if(!r.ok)throw new Error(j.error||('Lỗi '+r.status));return j;});
  });
}
function toast(msg,type){
  var el=document.createElement('div');
  el.className='toast '+(type||'ok');
  el.innerHTML='<span class="ic">'+(type==='err'?'⚠️':'✓')+'</span><span>'+esc(msg)+'</span>';
  $('toasts').appendChild(el);
  setTimeout(function(){el.style.transition='opacity .22s,transform .22s';el.style.opacity='0';el.style.transform='translateX(20px)';setTimeout(function(){el.remove();},220);},3200);
}
function dur(ms){var s=Math.round(ms/1000);if(s<60)return s+'s';var m=Math.floor(s/60);if(m<60)return m+'m';var h=Math.floor(m/60);if(h<48)return h+'h'+(m%60?' '+(m%60)+'m':'');var d=Math.floor(h/24);return d+'d'+(h%24?' '+(h%24)+'h':'');}
function durLong(ms){var s=Math.round(ms/1000);if(s<60)return s+' giây';var m=Math.floor(s/60);if(m<60)return m+' phút';var h=Math.floor(m/60);if(h<48)return h+' giờ'+(m%60?' '+(m%60)+' phút':'');var d=Math.floor(h/24);return d+' ngày'+(h%24?' '+(h%24)+' giờ':'');}
function ago(t){return t?dur(Date.now()-t)+' trước':'—';}
function pc(x){if(x<0)return '—';if(x>=99.995)return '100%';return x.toFixed(x>=99?2:1)+'%';}
function fmtMs(ms){if(!ms)return '—';if(ms<1000)return ms+' ms';return (ms/1000).toFixed(2)+' s';}

var _sgid=0;
function sparkline(pts,w,h){
  if(!pts||!pts.length)return '<div class="chart-empty">Chưa có dữ liệu</div>';
  var max=1;pts.forEach(function(p){if(p.up&&p.ms>max)max=p.ms;});
  var n=pts.length,dx=n>1?w/(n-1):0;
  var line='',marks='',brk=true,firstX=-1,lastX=-1;
  pts.forEach(function(p,i){
    var x=i*dx;
    if(p.up){var y=h-3-(p.ms/max)*(h-8);line+=(brk?'M':'L')+x.toFixed(1)+' '+y.toFixed(1)+' ';if(firstX<0)firstX=x;lastX=x;brk=false;}
    else{marks+='<rect x="'+(x-1).toFixed(1)+'" y="0" width="2" height="'+h+'" fill="currentColor" opacity=".35" rx="1"/>';brk=true;}
  });
  if(firstX<0)return '<div class="chart-empty">Chỉ toàn lỗi</div>';
  _sgid++;var gid='sg'+_sgid;
  var area=line+'L'+lastX.toFixed(1)+' '+h+' L'+firstX.toFixed(1)+' '+h+' Z';
  return '<svg viewBox="0 0 '+w+' '+h+'" width="100%" height="'+h+'" preserveAspectRatio="none"><defs><linearGradient id="'+gid+'" x1="0" x2="0" y1="0" y2="1"><stop offset="0%" stop-color="currentColor" stop-opacity=".22"/><stop offset="100%" stop-color="currentColor" stop-opacity="0"/></linearGradient></defs>'+marks+'<path d="'+area+'" fill="url(#'+gid+')"/><path d="'+line+'" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round" stroke-linecap="round"/></svg>';
}
function dayBar(days){
  return '<div class="day-bars">'+days.map(function(d){
    var bg,tip;
    if(d.pct<0){bg='var(--bg-subtle)';tip=d.date+': chưa có dữ liệu';}
    else if(d.pct>=99.9){bg='var(--up)';tip=d.date+': '+pc(d.pct);}
    else if(d.pct>=95){bg='var(--warn)';tip=d.date+': '+pc(d.pct);}
    else{bg='var(--down)';tip=d.date+': '+pc(d.pct);}
    return '<i title="'+esc(tip)+'" style="background:'+bg+'"></i>';
  }).join('')+'</div>';
}

var cache=[],open={},detail={},editId=null,checking={},sel={},filter={status:'all',q:''},sortBy='default';
var bannerDismissed=false;
var LABEL_FULL={up:'Hoạt động',down:'Sự cố',pending:'Đang chờ',paused:'Tạm dừng'};

// ---- sync indicator
function setSyncing(on){var el=$('sync');el.className='sync'+(on?' syncing':'');el.title=on?'Đang đồng bộ…':'Đã đồng bộ';}

// ---- favicon (title emoji)
function updateTitle(c){
  var e=c.down>0?'🔴':c.pending>0?'🟡':c.up>0?'🟢':'⚪';
  document.title=e+' Uptimer';
}

// ---- custom confirm
function confirm2(title,msg,okLabel){
  return new Promise(function(resolve){
    $('cfTitle').textContent=title;
    $('cfMsg').textContent=msg;
    $('cfOk').textContent=okLabel||'Xác nhận';
    $('confirmModal').classList.add('show');
    var done=false;
    function finish(v){if(done)return;done=true;$('confirmModal').classList.remove('show');resolve(v);}
    $('cfOk').onclick=function(){finish(true);};
    $('cfCancel').onclick=function(){finish(false);};
    $('confirmModal').onclick=function(e){if(e.target===$('confirmModal'))finish(false);};
  });
}

// ---- card content
function certBlock(m){
  if(!m.certExpiry)return '';
  var dd=Math.floor((m.certExpiry-Date.now())/86400000);
  var cls=dd<14?' danger':dd<30?' warn':'';
  return '<div><div class="metric-label">SSL</div><div class="metric-value'+cls+'">'+dd+' ngày</div></div>';
}
function errorBlock(m){
  if(!m.last||m.last.up)return '';
  return '<div style="grid-column:span 2"><div class="metric-label">Lỗi gần nhất</div><div class="metric-value danger" style="font-size:11.5px;line-height:1.3">'+esc(m.last.err||'lỗi')+'</div></div>';
}
function cardInner(m){
  var st=m.status;
  return '<div class="monitor-head">'+
      '<input type="checkbox" class="cb" data-cb="'+m.id+'"'+(sel[m.id]?' checked':'')+'>'+
      '<span class="status-dot '+st+'"></span>'+
      '<div class="monitor-info"><h3 class="monitor-name">'+esc(m.name)+'</h3><a class="monitor-url" href="'+esc(m.url)+'" target="_blank" rel="noopener">'+esc(m.url)+'</a></div>'+
      '<span class="badge '+st+'">'+LABEL_FULL[st]+'</span>'+
    '</div>'+
    '<div class="monitor-body">'+
      '<div class="metrics">'+
        '<div><div class="metric-label">24h</div><div class="metric-value">'+pc(m.up24)+'</div></div>'+
        '<div><div class="metric-label">7 ngày</div><div class="metric-value">'+pc(m.up7)+'</div></div>'+
        '<div><div class="metric-label">30 ngày</div><div class="metric-value">'+pc(m.up30)+'</div></div>'+
        '<div><div class="metric-label">TB phản hồi</div><div class="metric-value">'+fmtMs(m.avgMs)+'</div></div>'+
        certBlock(m)+errorBlock(m)+
      '</div>'+
      '<div class="sparkline">'+sparkline(m.spark,360,32)+'</div>'+
      dayBar(m.days)+
    '</div>'+
    '<div class="monitor-foot">'+
      '<div class="monitor-meta">'+
        '<span>Kiểm tra <b>'+ago(m.last&&m.last.t)+'</b></span>'+
        '<span>Từ <b>'+ago(m.since)+'</b></span>'+
        '<span>Chu kỳ <b>'+m.interval+'s</b></span>'+
      '</div>'+
      '<div class="monitor-actions">'+
        '<button class="btn btn-sm" data-a="detail" data-id="'+m.id+'">'+(open[m.id]?'▴':'▾')+'<span class="txt">'+(open[m.id]?'Ẩn':'Chi tiết')+'</span></button>'+
        '<button class="btn btn-sm" data-a="check" data-id="'+m.id+'"'+(checking[m.id]?' disabled':'')+'>'+(checking[m.id]?'<span class="spinner"></span>':'↻')+'<span class="txt">Check</span></button>'+
        '<button class="btn btn-sm" data-a="'+(m.paused?'resume':'pause')+'" data-id="'+m.id+'">'+(m.paused?'▶':'⏸')+'<span class="txt">'+(m.paused?'Tiếp':'Dừng')+'</span></button>'+
        '<button class="btn btn-sm" data-a="copy" data-id="'+m.id+'" title="Sao chép URL">⧉</button>'+
        '<button class="btn btn-sm" data-a="edit" data-id="'+m.id+'">✎<span class="txt">Sửa</span></button>'+
        '<button class="btn btn-sm btn-danger" data-a="del" data-id="'+m.id+'">🗑<span class="txt">Xoá</span></button>'+
      '</div>'+
    '</div>';
}
function card(m){
  return '<article class="monitor'+(sel[m.id]?' selected':'')+'" id="card-'+m.id+'" data-id="'+m.id+'" data-status="'+m.status+'">'+
    '<div class="body">'+cardInner(m)+'</div>'+
    '<div class="d-slot" id="d_'+m.id+'">'+(open[m.id]&&detail[m.id]?detail[m.id]:'')+'</div>'+
  '</article>';
}

function detailHTML(d){
  var h='<div class="detail">';
  h+='<div class="detail-section"><div class="detail-title">Thời gian phản hồi 24 giờ qua</div><div class="sparkline">'+(d.series&&d.series.length?sparkline(d.series,680,70):'<div class="chart-empty">Chưa có dữ liệu</div>')+'</div></div>';
  h+='<div class="detail-section"><div class="detail-title">Sự cố gần đây</div>';
  if(!d.incidents||!d.incidents.length){
    h+='<div style="color:var(--mut);font-size:12px">Chưa có sự cố nào 🎉</div>';
  } else {
    h+='<table class="incidents-table"><thead><tr><th>Bắt đầu</th><th>Kéo dài</th><th>Lý do</th></tr></thead><tbody>'+
      d.incidents.map(function(i){return '<tr><td>'+new Date(i.start).toLocaleString('vi-VN')+'</td><td>'+(i.end?durLong(i.end-i.start):'<b style="color:var(--down)">đang diễn ra</b>')+'</td><td>'+esc(i.reason)+'</td></tr>';}).join('')+'</tbody></table>';
  }
  return h+'</div></div>';
}

// ---- summary
function computeSummary(ms){
  var c={total:ms.length,up:0,down:0,paused:0,pending:0};
  var up30s=[],msSum=[];
  ms.forEach(function(m){
    c[m.status]=(c[m.status]||0)+1;
    if(m.up30>=0)up30s.push(m.up30);
    if(m.avgMs>0)msSum.push(m.avgMs);
  });
  c.avg30=up30s.length?up30s.reduce(function(a,b){return a+b;},0)/up30s.length:-1;
  c.avgMs=msSum.length?Math.round(msSum.reduce(function(a,b){return a+b;},0)/msSum.length):0;
  return c;
}

function sortArr(arr){
  if(sortBy==='name')return arr.slice().sort(function(a,b){return a.name.localeCompare(b.name);});
  if(sortBy==='status'){
    var order={down:0,pending:1,up:2,paused:3};
    return arr.slice().sort(function(a,b){return (order[a.status]||9)-(order[b.status]||9);});
  }
  if(sortBy==='uptime'){
    return arr.slice().sort(function(a,b){
      var au=a.up30<0?101:a.up30, bu=b.up30<0?101:b.up30;
      return au-bu;
    });
  }
  if(sortBy==='latency'){
    return arr.slice().sort(function(a,b){return (b.avgMs||0)-(a.avgMs||0);});
  }
  return arr;
}

function render(ms){
  var c=computeSummary(ms);
  var sumHTML=
    '<div class="summary-item"><div class="summary-label">Monitors</div><div class="summary-value">'+c.total+'</div></div>'+
    '<div class="summary-item"><div class="summary-label">Hoạt động</div><div class="summary-value '+(c.up>0?'up':'muted')+'">'+c.up+'</div></div>'+
    '<div class="summary-item"><div class="summary-label">Sự cố</div><div class="summary-value '+(c.down>0?'down':'muted')+'">'+c.down+'</div></div>'+
    '<div class="summary-item"><div class="summary-label">Uptime TB 30 ngày</div><div class="summary-value">'+(c.avg30>=0?pc(c.avg30):'—')+'</div></div>'+
    '<div class="summary-item"><div class="summary-label">Phản hồi TB</div><div class="summary-value">'+(c.avgMs?fmtMs(c.avgMs):'—')+'</div></div>';
  var sumEl=$('sum');
  if(sumEl.dataset.sig!==sumHTML){sumEl.innerHTML=sumHTML;sumEl.dataset.sig=sumHTML;}
  updateTitle(c);
  updateIncidentBanner(c);

  var list=$('list');
  if(!ms.length){
    if(!list.querySelector('.empty')){
      list.innerHTML='<div class="empty"><div class="empty-icon">📡</div><h3>Chưa có monitor nào</h3><p>Bấm <b>+ Thêm</b> để bắt đầu giám sát website, API hoặc TCP port.</p></div>';
    }
    return;
  }
  var ph=list.querySelector('.empty');
  if(ph)ph.remove();

  var ordered=sortArr(ms);
  var existing={};
  list.querySelectorAll('article.monitor').forEach(function(el){var id=el.dataset.id;if(id)existing[id]=el;});

  ordered.forEach(function(m){
    var el=existing[m.id];
    if(!el){
      var tmp=document.createElement('div');
      tmp.innerHTML=card(m);
      list.appendChild(tmp.firstElementChild);
    } else {
      if(el.dataset.status!==m.status)el.dataset.status=m.status;
      if(!checking[m.id]){
        var body=el.querySelector('.body');
        if(body)body.innerHTML=cardInner(m);
      }
    }
    delete existing[m.id];
  });
  Object.keys(existing).forEach(function(id){existing[id].remove();});

  // re-order DOM to match sorted order
  ordered.forEach(function(m){
    var el=$('card-'+m.id);
    if(el)list.appendChild(el);
  });

  applyFilter();
  syncBulk();
}

function updateIncidentBanner(c){
  var el=$('incBanner');
  if(bannerDismissed||c.down===0){el.hidden=true;return;}
  el.hidden=false;
  $('ibCount').textContent=c.down;
}

function applyFilter(){
  var total=cache.length,shown=0;
  document.querySelectorAll('article.monitor').forEach(function(el){
    var id=el.dataset.id;var m=null;
    for(var i=0;i<cache.length;i++){if(cache[i].id===id){m=cache[i];break;}}
    if(!m){el.style.display='none';return;}
    var show=true;
    if(filter.status!=='all'&&m.status!==filter.status)show=false;
    if(filter.q){
      var q=filter.q.toLowerCase();
      if((m.name+' '+m.url).toLowerCase().indexOf(q)<0)show=false;
    }
    el.style.display=show?'':'none';
    if(show)shown++;
  });
  var noMatch=$('list').querySelector('.no-match');
  if(shown===0&&total>0){
    if(!noMatch){
      noMatch=document.createElement('div');
      noMatch.className='no-match empty';
      noMatch.innerHTML='<div class="empty-icon">🔍</div><h3>Không có monitor phù hợp</h3><p>Thử đổi từ khoá hoặc bộ lọc.</p>';
      $('list').insertBefore(noMatch,$('list').firstChild);
    }
  } else if(noMatch){noMatch.remove();}
  var sub=$('sub');
  if(total===0)sub.textContent='Tổng quan sức khoẻ hệ thống';
  else if(shown===total)sub.textContent=total+' monitors được giám sát';
  else sub.textContent='Hiển thị '+shown+' trong '+total+' monitors';
}

// ---- bulk
function syncBulk(){
  var ids=Object.keys(sel).filter(function(k){return sel[k];});
  var n=ids.length;
  $('bulk').hidden=n===0;
  $('bulkCount').textContent=n;
  document.querySelectorAll('article.monitor').forEach(function(el){
    el.classList.toggle('selected',!!sel[el.dataset.id]);
    var cb=el.querySelector('.cb');
    if(cb)cb.checked=!!sel[el.dataset.id];
  });
}
function clearSel(){sel={};syncBulk();}

// ---- load
function loadDetail(id){
  api('GET','/api/monitors/'+id).then(function(d){
    var h=detailHTML(d);
    if(detail[id]===h)return;
    detail[id]=h;
    var el=$('d_'+id);
    if(el&&open[id])el.innerHTML=h;
  }).catch(function(){});
}
function load(){
  setSyncing(true);
  api('GET','/api/monitors').then(function(ms){
    cache=ms;render(ms);setSyncing(false);
    $('upd').textContent='Cập nhật lúc '+new Date().toLocaleTimeString('vi-VN');
    Object.keys(open).forEach(function(id){if(open[id])loadDetail(id);});
  }).catch(function(e){
    setSyncing(false);
    $('list').innerHTML='<div class="empty"><div class="empty-icon">⚠️</div><h3>Lỗi tải dữ liệu</h3><p>'+esc(e.message)+'</p></div>';
  });
}

// ---- form
function fsync(){
  var t=$('f_type').value;
  $('f_kwbox').style.display=t==='keyword'?'':'none';
  $('f_httpbox').style.display=t==='tcp'?'none':'';
  $('f_url_l').textContent=t==='tcp'?'Địa chỉ host:port':'URL';
  $('f_url').placeholder=t==='tcp'?'example.com:443':'https://example.com';
}
function openForm(m){
  editId=m?m.id:null;
  $('f_title').textContent=m?'Sửa monitor':'Thêm monitor';
  $('f_name').value=m?m.name:'';
  $('f_type').value=m?m.type:'http';
  $('f_url').value=m?m.url:'';
  $('f_int').value=m?m.interval:300;
  $('f_to').value=m?m.timeout:30;
  $('f_ret').value=m?m.retries:2;
  $('f_method').value=m?m.method:'GET';
  $('f_exp').value=m?m.expect:'200-399';
  $('f_kw').value=m?m.keyword:'';
  $('f_err').classList.remove('show');
  fsync();
  $('formModal').classList.add('show');
  setTimeout(function(){$('f_name').focus();},50);
}
function closeForm(){$('formModal').classList.remove('show');}
function saveForm(){
  var b={name:$('f_name').value,type:$('f_type').value,url:$('f_url').value,interval:+$('f_int').value,timeout:+$('f_to').value,retries:+$('f_ret').value,method:$('f_method').value,expect:$('f_exp').value,keyword:$('f_kw').value};
  api(editId?'PUT':'POST',editId?'/api/monitors/'+editId:'/api/monitors',b).then(function(){
    closeForm();toast(editId?'Đã cập nhật monitor':'Đã thêm monitor');load();
  }).catch(function(e){$('f_err').textContent=e.message;$('f_err').classList.add('show');});
}

// ---- cfg
function openCfg(){
  api('GET','/api/settings').then(function(c){
    $('c_title').value=c.title||'';
    $('c_web').value=c.webhook||'';
    $('c_dis').value=c.discord||'';
    $('c_tgt').value=c.tgToken||'';
    $('c_tgc').value=c.tgChat||'';
    $('c_pass').value='';$('c_pass2').value='';
    $('c_err').classList.remove('show');
    $('cfgModal').classList.add('show');
  });
}
function closeCfg(){$('cfgModal').classList.remove('show');}
function cfgBody(){
  var b={title:$('c_title').value,webhook:$('c_web').value,discord:$('c_dis').value,tgToken:$('c_tgt').value,tgChat:$('c_tgc').value};
  var np=$('c_pass').value;
  if(np){b.newPassword=np;b.confirmPassword=$('c_pass2').value;}
  return b;
}

// ---- command palette
var cmdActive=0;
function cmdActions(){
  return [
    {id:'add',label:'Thêm monitor mới',hint:'N',run:function(){closeCmd();openForm(null);}},
    {id:'cfg',label:'Mở cài đặt',hint:'',run:function(){closeCmd();openCfg();}},
    {id:'status',label:'Mở trang status công khai',hint:'',run:function(){closeCmd();var w=window.open('/status','_blank');if(!w||w.closed||typeof w.closed==='undefined'){location.href='/status';}}},
    {id:'refresh',label:'Làm mới dữ liệu',hint:'',run:function(){closeCmd();load();}},
    {id:'help',label:'Trợ giúp / phím tắt',hint:'?',run:function(){closeCmd();openHelp();}},
    {id:'logout',label:'Đăng xuất',hint:'',run:function(){location.href='/logout';}}
  ];
}
function renderCmd(q){
  q=(q||'').toLowerCase();
  var acts=cmdActions().filter(function(a){return a.label.toLowerCase().indexOf(q)>=0;});
  var mons=cache.filter(function(m){return (m.name+' '+m.url).toLowerCase().indexOf(q)>=0;}).slice(0,8);
  var html='';
  if(acts.length){
    html+='<div class="cmd-group">Hành động</div>';
    html+=acts.map(function(a,i){
      return '<div class="cmd-item'+(i===0?' active':'')+'" data-cmd="act" data-idx="'+i+'"><span>'+esc(a.label)+'</span>'+(a.hint?'<span class="k"><kbd>'+a.hint+'</kbd></span>':'')+'</div>';
    }).join('');
  }
  if(mons.length){
    html+='<div class="cmd-group">Monitors</div>';
    html+=mons.map(function(m){
      return '<div class="cmd-item" data-cmd="mon" data-id="'+m.id+'"><span class="status-dot '+m.status+'" style="margin-top:0;flex:none"></span><span>'+esc(m.name)+'</span><span class="k">'+esc(m.url)+'</span></div>';
    }).join('');
  }
  if(!acts.length&&!mons.length)html='<div class="cmd-empty">Không có kết quả cho "'+esc(q)+'"</div>';
  $('cmdList').innerHTML=html;
  cmdActive=0;
}
function openCmd(){$('cmdModal').classList.add('show');$('cmdInput').value='';renderCmd('');setTimeout(function(){$('cmdInput').focus();},40);}
function closeCmd(){$('cmdModal').classList.remove('show');}
function moveCmd(d){
  var items=$('cmdList').querySelectorAll('.cmd-item');
  if(!items.length)return;
  cmdActive=(cmdActive+d+items.length)%items.length;
  items.forEach(function(el,i){el.classList.toggle('active',i===cmdActive);});
  items[cmdActive].scrollIntoView({block:'nearest'});
}
function openHelp(){$('helpModal').classList.add('show');}
function closeHelp(){$('helpModal').classList.remove('show');}

// ---- event handlers
$('f_type').onchange=fsync;
$('add').onclick=function(){openForm(null);};
$('f_cancel').onclick=closeForm;
$('f_save').onclick=saveForm;
$('c_close').onclick=closeCfg;
$('c_save').onclick=function(){
  api('PUT','/api/settings',cfgBody()).then(function(){
    var changed=!!$('c_pass').value;
    toast(changed?'Đã đổi mật khẩu — vui lòng đăng nhập lại':'Đã lưu cài đặt');
    if(changed){setTimeout(function(){location.href='/login';},800);}
    else{closeCfg();}
  }).catch(function(e){$('c_err').textContent=e.message;$('c_err').classList.add('show');});
};
$('c_test').onclick=function(){
  api('PUT','/api/settings',cfgBody()).then(function(){return api('POST','/api/test-alert');}).then(function(){
    toast('Đã gửi tin thử — kiểm tra kênh nhận');
  }).catch(function(e){$('c_err').textContent=e.message;$('c_err').classList.add('show');});
};
$('cmdBtn').onclick=openCmd;
$('helpClose').onclick=closeHelp;

// user menu
$('userBtn').onclick=function(e){e.stopPropagation();$('userDrop').classList.toggle('show');};
document.addEventListener('click',function(e){
  if(!$('userMenu').contains(e.target))$('userDrop').classList.remove('show');
});
$('userDrop').onclick=function(e){
  $('userDrop').classList.remove('show');
  var b=e.target.closest('button, a[data-mm]');if(!b)return;
  var m=b.getAttribute('data-mm');
  if(m==='cfg')openCfg();
  else if(m==='help')openHelp();
  else if(m==='logout')location.href='/logout';
  else if(m==='status'){
    var w = window.open('/status', '_blank');
    if (!w) location.href = '/status';
  }
};

// incident banner
$('ibView').onclick=function(){
  filter.status='down';
  document.querySelectorAll('#filters button').forEach(function(x){x.classList.toggle('active',x.getAttribute('data-f')==='down');});
  applyFilter();
};
$('ibClose').onclick=function(){bannerDismissed=true;$('incBanner').hidden=true;};

// list actions
$('list').onclick=function(e){
  var cb=e.target.closest('.cb');
  if(cb){
    var id=cb.getAttribute('data-cb');
    sel[id]=cb.checked;
    syncBulk();
    return;
  }
  var b=e.target.closest('button');
  if(!b)return;
  var id=b.getAttribute('data-id'),a=b.getAttribute('data-a');
  if(!id||!a)return;
  if(a==='detail'){
    open[id]=!open[id];
    if(open[id])loadDetail(id);
    else{var d=$('d_'+id);if(d)d.innerHTML='';}
    render(cache);
  }
  else if(a==='edit'){cache.forEach(function(m){if(m.id===id)openForm(m);});}
  else if(a==='copy'){
    var m=cache.filter(function(x){return x.id===id;})[0];
    if(m&&navigator.clipboard){navigator.clipboard.writeText(m.url).then(function(){toast('Đã sao chép URL');});}
  }
  else if(a==='del'){
    confirm2('Xoá monitor','Xoá monitor này và toàn bộ lịch sử?','Xoá').then(function(ok){
      if(!ok)return;
      api('DELETE','/api/monitors/'+id).then(function(){toast('Đã xoá');delete sel[id];load();}).catch(function(e){toast(e.message,'err');});
    });
  } else if(a==='check'){
    if(checking[id])return;
    checking[id]=true;b.disabled=true;
    b.innerHTML='<span class="spinner"></span><span class="txt">Check</span>';
    api('POST','/api/monitors/'+id+'/check').then(function(){delete checking[id];toast('Đã kiểm tra');load();}).catch(function(){delete checking[id];load();});
  } else {
    api('POST','/api/monitors/'+id+'/'+a).then(function(){toast(a==='pause'?'Đã tạm dừng':'Đã tiếp tục');load();}).catch(function(e){toast(e.message,'err');});
  }
};

// bulk actions
$('bulkClear').onclick=clearSel;
$('bulk').addEventListener('click',function(e){
  var b=e.target.closest('button[data-bulk]');if(!b)return;
  var action=b.getAttribute('data-bulk');
  var ids=Object.keys(sel).filter(function(k){return sel[k];});
  if(!ids.length)return;
  if(action==='del'){
    confirm2('Xoá '+ids.length+' monitor','Xoá các monitor đã chọn và toàn bộ lịch sử?','Xoá '+ids.length).then(function(ok){
      if(!ok)return;
      var promises=ids.map(function(id){return api('DELETE','/api/monitors/'+id).catch(function(){});});
      Promise.all(promises).then(function(){ids.forEach(function(id){delete sel[id];});toast('Đã xoá '+ids.length+' monitor');load();});
    });
    return;
  }
  var promises=ids.map(function(id){return api('POST','/api/monitors/'+id+'/'+action).catch(function(){});});
  Promise.all(promises).then(function(){
    toast('Đã '+({check:'check',pause:'tạm dừng',resume:'tiếp tục'}[action]||action)+' '+ids.length+' monitor');
    load();
  });
});

// search / filter / sort
$('q').addEventListener('input',function(){filter.q=this.value.trim();applyFilter();});
$('filters').addEventListener('click',function(e){
  var b=e.target.closest('button');if(!b)return;
  $('filters').querySelectorAll('button').forEach(function(x){x.classList.remove('active');});
  b.classList.add('active');filter.status=b.getAttribute('data-f');applyFilter();
});
$('sort').addEventListener('change',function(){sortBy=this.value;render(cache);});

// modals backdrop
document.querySelectorAll('.modal').forEach(function(m){
  m.addEventListener('click',function(e){if(e.target===m)m.classList.remove('show');});
});

// keybindings
document.addEventListener('keydown',function(e){
  var isInput=/^(input|select|textarea)$/i.test(e.target.tagName);
  // Esc
  if(e.key==='Escape'){
    if($('cmdModal').classList.contains('show')){closeCmd();return;}
    if($('formModal').classList.contains('show')){closeForm();return;}
    if($('cfgModal').classList.contains('show')){closeCfg();return;}
    if($('helpModal').classList.contains('show')){closeHelp();return;}
    if($('confirmModal').classList.contains('show')){$('cfCancel').click();return;}
    $('userDrop').classList.remove('show');
    return;
  }
  // Cmd+K / Ctrl+K
  if((e.metaKey||e.ctrlKey)&&e.key.toLowerCase()==='k'){
    e.preventDefault();
    if($('cmdModal').classList.contains('show'))closeCmd();else openCmd();
    return;
  }
  if(isInput)return;
  if($('cmdModal').classList.contains('show')||$('formModal').classList.contains('show')||$('cfgModal').classList.contains('show'))return;
  // N
  if(e.key==='n'||e.key==='N'){e.preventDefault();openForm(null);return;}
  // /
  if(e.key==='/'){e.preventDefault();$('q').focus();return;}
  // ?
  if(e.key==='?'){e.preventDefault();openHelp();return;}
});

// command palette input
$('cmdInput').addEventListener('input',function(){renderCmd(this.value);});
$('cmdInput').addEventListener('keydown',function(e){
  if(e.key==='ArrowDown'){e.preventDefault();moveCmd(1);}
  else if(e.key==='ArrowUp'){e.preventDefault();moveCmd(-1);}
  else if(e.key==='Enter'){
    e.preventDefault();
    var item=$('cmdList').querySelectorAll('.cmd-item')[cmdActive];
    if(item)item.click();
  }
});
$('cmdList').addEventListener('click',function(e){
  var item=e.target.closest('.cmd-item');if(!item)return;
  var type=item.getAttribute('data-cmd');
  if(type==='act'){
    var acts=cmdActions();
    var idx=+item.getAttribute('data-idx');
    if(acts[idx])acts[idx].run();
  } else if(type==='mon'){
    var id=item.getAttribute('data-id');
    closeCmd();
    if(!open[id]){open[id]=true;loadDetail(id);render(cache);}
    var el=$('card-'+id);
    if(el){el.scrollIntoView({behavior:'smooth',block:'center'});el.style.outline='2px solid var(--accent)';setTimeout(function(){el.style.outline='';},1500);}
  }
});

// form Enter-to-save
$('formModal').addEventListener('keydown',function(e){
  if(e.key==='Enter'&&e.target.tagName==='INPUT'){e.preventDefault();saveForm();}
});


// Reliable status page opener
document.querySelectorAll('a[href="/status"], button[data-mm="status"]').forEach(function(el){
  el.addEventListener('click', function(e){
    e.preventDefault();
    e.stopPropagation();
    var w = window.open('/status', '_blank');
    if (!w) location.href = '/status';
  });
});

load();
setInterval(load,10000);
</script></body></html>`

const statusHTML = `<!doctype html>
<html lang="vi"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Trạng thái hệ thống</title>
<style>
:root{
  --bg:#fafafa;--bg-subtle:#f4f4f5;--card:#fff;
  --border:#e5e7eb;--border-strong:#d1d5db;
  --fg:#09090b;--mut:#71717a;--mut-subtle:#a1a1aa;
  --up:#059669;--up-bg:#ecfdf5;--up-bd:#a7f3d0;
  --down:#dc2626;--down-bg:#fef2f2;--down-bd:#fecaca;
  --warn:#d97706;--warn-bg:#fffbeb;--warn-bd:#fde68a;
  --pause:#71717a;--pause-bg:#f4f4f5;--pause-bd:#e5e7eb;
  --focus:rgba(79,70,229,.2);--sh:0 1px 2px rgba(0,0,0,.05);
}
@media(prefers-color-scheme:dark){
  :root{
    --bg:#09090b;--bg-subtle:#18181b;--card:#0c0c0f;
    --border:#27272a;--border-strong:#3f3f46;
    --fg:#fafafa;--mut:#a1a1aa;--mut-subtle:#71717a;
    --up:#10b981;--up-bg:rgba(16,185,129,.1);--up-bd:rgba(16,185,129,.3);
    --down:#ef4444;--down-bg:rgba(239,68,68,.1);--down-bd:rgba(239,68,68,.3);
    --warn:#f59e0b;--warn-bg:rgba(245,158,11,.1);--warn-bd:rgba(245,158,11,.3);
    --pause:#71717a;--pause-bg:rgba(113,113,122,.15);--pause-bd:rgba(113,113,122,.3);
    --focus:rgba(129,140,248,.25);--sh:0 1px 2px rgba(0,0,0,.4);
  }
}
:root[data-theme="light"]{
  --bg:#fafafa;--bg-subtle:#f4f4f5;--card:#fff;
  --border:#e5e7eb;--border-strong:#d1d5db;
  --fg:#09090b;--mut:#71717a;--mut-subtle:#a1a1aa;
  --up:#059669;--up-bg:#ecfdf5;--up-bd:#a7f3d0;
  --down:#dc2626;--down-bg:#fef2f2;--down-bd:#fecaca;
  --warn:#d97706;--warn-bg:#fffbeb;--warn-bd:#fde68a;
  --pause:#71717a;--pause-bg:#f4f4f5;--pause-bd:#e5e7eb;
  --focus:rgba(79,70,229,.2);--sh:0 1px 2px rgba(0,0,0,.05);
}
:root[data-theme="dark"]{
  --bg:#09090b;--bg-subtle:#18181b;--card:#0c0c0f;
  --border:#27272a;--border-strong:#3f3f46;
  --fg:#fafafa;--mut:#a1a1aa;--mut-subtle:#71717a;
  --up:#10b981;--up-bg:rgba(16,185,129,.1);--up-bd:rgba(16,185,129,.3);
  --down:#ef4444;--down-bg:rgba(239,68,68,.1);--down-bd:rgba(239,68,68,.3);
  --warn:#f59e0b;--warn-bg:rgba(245,158,11,.1);--warn-bd:rgba(245,158,11,.3);
  --pause:#71717a;--pause-bg:rgba(113,113,122,.15);--pause-bd:rgba(113,113,122,.3);
  --focus:rgba(129,140,248,.25);--sh:0 1px 2px rgba(0,0,0,.4);
}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:13.5px/1.55 ui-sans-serif,system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;-webkit-font-smoothing:antialiased;font-feature-settings:"cv02","cv03","cv04","cv11";transition:background .2s,color .2s}
.wrap{max-width:800px;margin:0 auto;padding:36px 20px}
.top-row{display:flex;justify-content:space-between;align-items:flex-start;gap:16px;margin-bottom:4px}
h1{font-size:22px;font-weight:600;letter-spacing:-0.02em;margin:0}
.sub{color:var(--mut);font-size:12.5px;margin:0 0 24px}
.theme-toggle{background:var(--card);border:1px solid var(--border);border-radius:6px;padding:6px 10px;font-size:12px;color:var(--fg);cursor:pointer;display:inline-flex;align-items:center;gap:6px}
.theme-toggle:hover{border-color:var(--border-strong)}
.theme-toggle:focus{outline:none;box-shadow:0 0 0 3px var(--focus)}
.health{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:18px 20px;margin-bottom:16px;display:flex;gap:16px;align-items:center;flex-wrap:wrap;box-shadow:var(--sh)}
.health-badge{display:inline-flex;align-items:center;gap:8px;padding:6px 14px;border-radius:6px;font-weight:600;font-size:13px;border:1px solid}
.health-badge.up{color:var(--up);background:var(--up-bg);border-color:var(--up-bd)}
.health-badge.down{color:var(--down);background:var(--down-bg);border-color:var(--down-bd)}
.health-badge.loading{color:var(--mut);background:var(--bg-subtle);border-color:var(--border)}
.health-badge::before{content:"";width:8px;height:8px;border-radius:50%;background:currentColor}
.health-stats{display:flex;gap:24px;flex-wrap:wrap;font-size:12.5px;color:var(--mut);margin-left:auto}
.health-stat{display:flex;flex-direction:column}
.health-stat b{color:var(--fg);font-weight:600;font-variant-numeric:tabular-nums}
.filters{display:flex;gap:2px;margin-bottom:12px;padding:2px;background:var(--bg-subtle);border-radius:6px;border:1px solid var(--border);width:fit-content}
.filters button{height:26px;padding:0 12px;font-size:11.5px;font-weight:500;border:none;background:transparent;color:var(--mut);border-radius:4px;cursor:pointer;transition:background .1s,color .1s;line-height:1}
.filters button:hover{color:var(--fg)}
.filters button.active{background:var(--card);color:var(--fg);box-shadow:0 1px 2px rgba(0,0,0,.06)}
.card{background:var(--card);border:1px solid var(--border);border-radius:10px;padding:14px 16px;margin-bottom:8px;box-shadow:var(--sh);transition:border-color .12s}
.card:hover{border-color:var(--border-strong)}
.card.down{border-color:var(--down-bd)}
.card[hidden]{display:none}
.top{display:flex;justify-content:space-between;align-items:center;gap:12px;margin-bottom:8px}
.top h3{margin:0;font-size:13.5px;font-weight:600;letter-spacing:-0.01em;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.st{font-weight:600;font-size:10.5px;padding:2px 8px;border-radius:4px;border:1px solid;display:inline-flex;align-items:center;gap:5px;flex:none;white-space:nowrap;line-height:1.4}
.st::before{content:"";width:4px;height:4px;border-radius:50%;background:currentColor}
.st.up{background:var(--up-bg);color:var(--up);border-color:var(--up-bd)}
.st.down{background:var(--down-bg);color:var(--down);border-color:var(--down-bd)}
.st.pending{background:var(--warn-bg);color:var(--warn);border-color:var(--warn-bd)}
.st.paused{background:var(--pause-bg);color:var(--pause);border-color:var(--pause-bd)}
.days{display:flex;gap:2px;height:24px;margin-top:8px}
.days i{flex:1;border-radius:2px;transition:transform .12s,opacity .12s;cursor:default;min-width:0}
.days i:hover{transform:scaleY(1.15);opacity:.85}
.meta{display:flex;justify-content:space-between;margin-top:8px;font-size:11.5px;color:var(--mut);flex-wrap:wrap;gap:6px;font-variant-numeric:tabular-nums}
.meta b{color:var(--fg);font-weight:500}
.meta .danger{color:var(--down)}
.foot{text-align:center;color:var(--mut);font-size:11px;margin-top:28px}
.foot a{color:var(--mut);text-decoration:none;border-bottom:1px dashed var(--border-strong)}
.foot a:hover{color:var(--fg)}
@media(prefers-reduced-motion:reduce){*,*::before,*::after{animation-duration:.01ms!important;transition-duration:.01ms!important}}
</style></head><body><div class="wrap">
<div class="top-row">
  <div>
    <h1 id="t">Trạng thái hệ thống</h1>
    <p class="sub" id="sub">Đang tải dữ liệu…</p>
  </div>
  <button class="theme-toggle" id="themeBtn" title="Đổi giao diện">
    <span id="themeIcon">◐</span><span id="themeLabel">Hệ thống</span>
  </button>
</div>

<div class="health">
  <span class="health-badge loading" id="hb">Đang tải…</span>
  <div class="health-stats">
    <div class="health-stat"><span>Uptime TB 30 ngày</span><b id="hsUp30">—</b></div>
    <div class="health-stat"><span>Monitors</span><b id="hsCount">—</b></div>
  </div>
</div>

<div class="filters" id="filters">
  <button data-f="all" class="active">Tất cả</button>
  <button data-f="up">Hoạt động</button>
  <button data-f="down">Sự cố</button>
</div>

<div id="list"></div>
<p class="foot" id="upd">Đang tải…</p>
</div>
<script>
var $=function(i){return document.getElementById(i)};
function esc(s){return String(s==null?'':s).replace(/[&<>"']/g,function(c){return ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'})[c];});}
function pc(x){if(x<0)return '—';if(x>=99.995)return '100%';return x.toFixed(x>=99?2:1)+'%';}
var LABEL={up:'Hoạt động',down:'Sự cố',pending:'Đang chờ',paused:'Tạm dừng'};
var lastJSON='',filterStatus='all';

// theme
function applyTheme(t){
  var label,icon;
  if(t==='light'){icon='☀';label='Sáng';document.documentElement.setAttribute('data-theme','light');}
  else if(t==='dark'){icon='☾';label='Tối';document.documentElement.setAttribute('data-theme','dark');}
  else{icon='◐';label='Hệ thống';document.documentElement.removeAttribute('data-theme');}
  $('themeIcon').textContent=icon;$('themeLabel').textContent=label;
  try{localStorage.setItem('theme',t);}catch(e){}
}
$('themeBtn').onclick=function(){
  var cur=localStorage.getItem('theme')||'system';
  var next=cur==='system'?'light':cur==='light'?'dark':'system';
  applyTheme(next);
};
(function(){var t;try{t=localStorage.getItem('theme');}catch(e){}
  if(t)applyTheme(t);})();

function renderCard(m){
  var bars=m.days.map(function(x){
    var c;
    if(x.pct<0)c='var(--bg-subtle)';
    else if(x.pct>=99.9)c='var(--up)';
    else if(x.pct>=95)c='var(--warn)';
    else c='var(--down)';
    return '<i title="'+esc(x.date)+': '+pc(x.pct)+'" style="background:'+c+'"></i>';
  }).join('');
  var downFor=m.status==='down'&&m.since?'<span class="danger">Đang sự cố <b>'+Math.floor((Date.now()-m.since)/60000)+' phút</b></span>':'';
  return '<div class="top"><h3>'+esc(m.name)+'</h3><span class="st '+m.status+'">'+(LABEL[m.status]||m.status)+'</span></div>'+
    '<div class="days">'+bars+'</div>'+
    '<div class="meta"><span>Uptime 30 ngày: <b>'+pc(m.up30)+'</b></span>'+downFor+'</div>';
}

function render(d){
  var bad=d.overall==='down';
  var hb=$('hb');
  var want=bad?'down':'up';
  if(hb.dataset.state!==want){
    hb.className='health-badge '+want;
    hb.textContent=bad?'Một số dịch vụ gặp sự cố':'Tất cả hoạt động bình thường';
    hb.dataset.state=want;
  }
  // uptime avg
  var ups=d.items.filter(function(x){return x.up30>=0;}).map(function(x){return x.up30;});
  var avg=ups.length?ups.reduce(function(a,b){return a+b;},0)/ups.length:-1;
  $('hsUp30').textContent=avg>=0?pc(avg):'—';
  $('hsCount').textContent=d.items.length;
  $('sub').textContent=d.items.length+' dịch vụ được giám sát';
  document.title=(bad?'🔴 ':'🟢 ')+d.title;

  var list=$('list');
  if(!d.items.length){list.innerHTML='';return;}

  var existing={};
  list.querySelectorAll('.card').forEach(function(el){if(el.dataset.id)existing[el.dataset.id]=el;});

  d.items.forEach(function(m,idx){
    var key=m.name+'|'+idx;
    var html=renderCard(m);
    var el=existing[key];
    if(!el){
      var div=document.createElement('div');
      div.className='card'+(m.status==='down'?' down':'');
      div.dataset.id=key;
      div.dataset.status=m.status;
      div.innerHTML=html;
      list.appendChild(div);
    } else {
      if((el.classList.contains('down'))!==(m.status==='down')){
        el.classList.toggle('down',m.status==='down');
      }
      el.dataset.status=m.status;
      if(el.innerHTML!==html)el.innerHTML=html;
    }
    delete existing[key];
  });
  Object.keys(existing).forEach(function(k){existing[k].remove();});
  applyFilter();
}

function applyFilter(){
  document.querySelectorAll('.card').forEach(function(el){
    var show=filterStatus==='all'||el.dataset.status===filterStatus;
    if(show)el.removeAttribute('hidden');else el.setAttribute('hidden','');
  });
}

function load(){
  fetch('/status.json').then(function(r){return r.json();}).then(function(d){
    $('t').textContent=d.title;
    var j=JSON.stringify(d.items);
    if(j!==lastJSON){
      lastJSON=j;render(d);
    } else {
      document.querySelectorAll('.card').forEach(function(el,idx){
        var m=d.items[idx];if(!m)return;
        if(m.status==='down'&&m.since){
          var span=el.querySelector('.meta .danger b');
          if(span)span.textContent=Math.floor((Date.now()-m.since)/60000)+' phút';
        }
      });
    }
    $('upd').textContent='Cập nhật lúc '+new Date(d.time).toLocaleString('vi-VN')+' · tự động mỗi 30 giây';
  }).catch(function(){
    var hb=$('hb');
    hb.className='health-badge loading';
    hb.textContent='Không tải được dữ liệu';
  });
}

$('filters').addEventListener('click',function(e){
  var b=e.target.closest('button');if(!b)return;
  $('filters').querySelectorAll('button').forEach(function(x){x.classList.remove('active');});
  b.classList.add('active');filterStatus=b.getAttribute('data-f');applyFilter();
});

load();setInterval(load,30000);
</script></body></html>`
