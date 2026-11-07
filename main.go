// uptimer - web server giám sát uptime kiểu UptimeRobot (1 file, không cần thư viện ngoài)
//
// Chạy:
//   go build -o uptimer && ./uptimer -seed https://pixpack.onrender.com
//   rồi mở http://localhost:8288  (đăng nhập mặc định: admin / admin)
//
// Tính năng: HTTP / từ khoá / TCP, chu kỳ từ 30 giây, thử lại trước khi báo DOWN,
// uptime 24h/7d/30d, thời gian phản hồi, hạn SSL, lịch sử sự cố, cảnh báo
// (Telegram, Discord, webhook), trang status công khai tại /status.
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
:root{--bg:#0f172a;--fg:#f1f5f9;--mut:#94a3b8;--card:#1e293b;--bd:#334155;--acc:#3b82f6;--err:#ef4444}
@media(prefers-color-scheme:light){:root{--bg:#f8fafc;--fg:#0f172a;--mut:#64748b;--card:#fff;--bd:#e2e8f0}}
*{box-sizing:border-box}
body{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;
 background:radial-gradient(circle at 20% 20%,#1e3a8a22,transparent 40%),radial-gradient(circle at 80% 80%,#7c3aed22,transparent 40%),var(--bg);
 color:var(--fg);font:15px/1.55 system-ui,-apple-system,sans-serif;padding:20px}
.box{background:var(--card);border:1px solid var(--bd);border-radius:20px;padding:36px 32px;width:100%;max-width:400px;box-shadow:0 25px 50px -12px rgb(0 0 0 / .35)}
.logo{width:56px;height:56px;border-radius:16px;background:linear-gradient(135deg,#3b82f6,#7c3aed);display:flex;align-items:center;justify-content:center;font-size:28px;margin:0 auto 20px;box-shadow:0 10px 20px -5px rgb(59 130 246 / .5)}
h1{margin:0 0 6px;font-size:24px;text-align:center;font-weight:800;letter-spacing:-.02em}
.sub{margin:0 0 24px;text-align:center;color:var(--mut);font-size:14px}
label{display:block;margin-top:14px;font-weight:600;font-size:13.5px}
input{width:100%;padding:12px 14px;border:1px solid var(--bd);border-radius:12px;background:var(--bg);color:var(--fg);margin-top:6px;font:inherit;transition:border-color .15s,box-shadow .15s}
input:focus{outline:none;border-color:var(--acc);box-shadow:0 0 0 3px rgb(59 130 246 / .2)}
button{width:100%;margin-top:20px;padding:13px;background:linear-gradient(135deg,#3b82f6,#2563eb);color:#fff;border:none;border-radius:12px;font:inherit;font-weight:700;cursor:pointer;transition:transform .1s,box-shadow .15s}
button:hover{box-shadow:0 10px 15px -3px rgb(59 130 246 / .4)}
button:active{transform:translateY(1px)}
.err{background:rgba(239,68,68,.12);color:var(--err);padding:10px 14px;border-radius:10px;margin-bottom:16px;font-size:13.5px;text-align:center;border:1px solid rgba(239,68,68,.2)}
.foot{margin-top:20px;text-align:center;color:var(--mut);font-size:12px}
</style></head><body>
<div class="box">
<div class="logo">📡</div>
<h1>Uptimer</h1>
<p class="sub">Đăng nhập để quản trị hệ thống</p>
` + errHTML + `
<form method="POST" action="/login">
<label>Tên đăng nhập</label>
<input name="user" value="admin" autocomplete="username" required autofocus>
<label>Mật khẩu</label>
<input name="pass" type="password" autocomplete="current-password" placeholder="Mặc định: admin" required>
<button type="submit">Đăng nhập →</button>
</form>
<p class="foot">Giám sát uptime tự host · không cần cài đặt</p>
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
  --bg:#f8fafc;--fg:#0f172a;--mut:#64748b;--card:#ffffff;--bd:#e2e8f0;
  --up:#16a34a;--down:#dc2626;--pend:#d97706;--pause:#94a3b8;--acc:#2563eb;
  --up-bg:#dcfce7;--down-bg:#fee2e2;--pend-bg:#fef3c7;--acc-bg:#dbeafe;
  --sh:0 1px 3px 0 rgb(0 0 0 / .1),0 1px 2px -1px rgb(0 0 0 / .1);
  --sh-md:0 4px 6px -1px rgb(0 0 0 / .1),0 2px 4px -2px rgb(0 0 0 / .1);
  --sh-lg:0 10px 15px -3px rgb(0 0 0 / .1),0 4px 6px -4px rgb(0 0 0 / .1);
  --r:14px;
}
@media(prefers-color-scheme:dark){
  :root{
    --bg:#0b1220;--fg:#e2e8f0;--mut:#94a3b8;--card:#152033;--bd:#1e293b;
    --up-bg:rgba(22,163,74,.12);--down-bg:rgba(220,38,38,.12);--pend-bg:rgba(217,119,6,.12);
    --sh:0 1px 3px 0 rgb(0 0 0 / .4),0 1px 2px -1px rgb(0 0 0 / .4);
    --sh-md:0 4px 6px -1px rgb(0 0 0 / .4),0 2px 4px -2px rgb(0 0 0 / .4);
    --sh-lg:0 10px 15px -3px rgb(0 0 0 / .5),0 4px 6px -4px rgb(0 0 0 / .5);
  }
}
*{box-sizing:border-box}
html,body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.55 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;-webkit-font-smoothing:antialiased}
a{color:var(--acc);text-decoration:none}
a:hover{text-decoration:underline}
.wrap{max-width:960px;margin:0 auto;padding:20px}
header.top{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-bottom:20px;padding-bottom:16px;border-bottom:1px solid var(--bd)}
.brand{display:flex;align-items:center;gap:10px;font-size:20px;font-weight:800;letter-spacing:-.02em;margin:0}
.logo{display:inline-flex;width:34px;height:34px;background:linear-gradient(135deg,#2563eb,#7c3aed);border-radius:10px;align-items:center;justify-content:center;font-size:17px;box-shadow:var(--sh-md)}
.actions{display:flex;gap:8px;flex-wrap:wrap}
button,.btn{font:inherit;cursor:pointer;border:1px solid var(--bd);background:var(--card);color:var(--fg);padding:8px 14px;border-radius:10px;transition:all .15s;font-weight:600;font-size:14px;display:inline-flex;align-items:center;gap:6px;text-decoration:none}
button:hover,.btn:hover{background:var(--bg);text-decoration:none}
button:active{transform:translateY(1px)}
button:disabled{opacity:.5;cursor:not-allowed}
button.pri{background:var(--acc);color:#fff;border-color:var(--acc)}
button.pri:hover{background:#1d4ed8}
button.dng{color:var(--down);border-color:var(--down)}
button.dng:hover{background:var(--down-bg)}
button.icon{padding:8px 10px;font-size:15px}
.sum{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:10px;margin:20px 0}
.stat{background:var(--card);border:1px solid var(--bd);border-radius:var(--r);padding:14px 16px;box-shadow:var(--sh);transition:transform .15s,box-shadow .15s}
.stat:hover{transform:translateY(-2px);box-shadow:var(--sh-md)}
.stat-val{font-size:24px;font-weight:800;letter-spacing:-.02em;line-height:1.1}
.stat-lbl{color:var(--mut);font-size:12.5px;font-weight:600;text-transform:uppercase;letter-spacing:.04em;margin-top:4px}
.stat.up .stat-val{color:var(--up)}
.stat.down .stat-val{color:var(--down)}
.stat.pend .stat-val{color:var(--pend)}
.card{background:var(--card);border:1px solid var(--bd);border-radius:var(--r);padding:16px 18px;margin-bottom:12px;box-shadow:var(--sh);transition:box-shadow .2s,border-color .2s;animation:rise .25s ease-out}
.card:hover{box-shadow:var(--sh-md)}
.card[data-status="down"]{border-left:3px solid var(--down)}
.card[data-status="up"]{border-left:3px solid var(--up)}
.card[data-status="paused"]{border-left:3px solid var(--pause);opacity:.75}
.card[data-status="pending"]{border-left:3px solid var(--pend)}
@keyframes rise{from{opacity:0;transform:translateY(4px)}}
.card-head{display:flex;align-items:flex-start;gap:12px}
.dot{width:12px;height:12px;border-radius:50%;flex:none;background:var(--pause);margin-top:7px;box-shadow:0 0 0 3px var(--card)}
.dot.up{background:var(--up)}
.dot.down{background:var(--down);animation:pulse 1.4s infinite}
.dot.pending{background:var(--pend);animation:pulse 2s infinite}
@keyframes pulse{0%,100%{opacity:1;transform:scale(1)}50%{opacity:.5;transform:scale(.9)}}
.card-title{flex:1;min-width:0}
.card-title h3{margin:0;font-size:16px;font-weight:700;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;letter-spacing:-.01em}
.card-title .url{font-size:12.5px;color:var(--mut);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;display:block;margin-top:2px;font-family:ui-monospace,SFMono-Regular,monospace}
.badge{font-size:11px;font-weight:800;padding:3px 10px;border-radius:8px;color:#fff;background:var(--pause);letter-spacing:.04em}
.badge.up{background:var(--up)}
.badge.down{background:var(--down)}
.badge.pending{background:var(--pend)}
.metrics{display:flex;flex-wrap:wrap;gap:6px 18px;margin:14px 0;font-size:13px;color:var(--mut)}
.metrics .m{display:flex;flex-direction:column}
.metrics .m b{font-weight:700;color:var(--fg);font-size:15px;line-height:1.2}
.metrics .m.warn b{color:var(--pend)}
.metrics .m.danger b{color:var(--down)}
.chart{margin:10px 0 4px}
.chart svg{display:block;width:100%;height:32px}
.days{display:flex;gap:2px;height:24px;margin-top:8px}
.days i{flex:1;border-radius:3px;transition:transform .15s}
.days i:hover{transform:scaleY(1.15)}
.card-actions{display:flex;gap:6px;flex-wrap:wrap;margin-top:14px;padding-top:12px;border-top:1px solid var(--bd)}
.card-actions button{font-size:13px;padding:6px 11px}
.detail{margin-top:14px;padding-top:14px;border-top:1px solid var(--bd);animation:rise .2s}
.detail h4{margin:0 0 8px;font-size:12.5px;font-weight:700;color:var(--mut);text-transform:uppercase;letter-spacing:.05em}
.detail table{width:100%;border-collapse:collapse;font-size:13px;margin-top:4px}
.detail td{padding:8px 10px;border-bottom:1px solid var(--bd);vertical-align:top}
.detail tr:last-child td{border-bottom:none}
.empty{text-align:center;padding:60px 20px;color:var(--mut)}
.empty-icon{font-size:48px;margin-bottom:12px;opacity:.5}
.empty h3{margin:0 0 8px;color:var(--fg);font-size:18px}
footer.bar{margin-top:24px;padding-top:16px;border-top:1px solid var(--bd);display:flex;justify-content:space-between;color:var(--mut);font-size:12.5px;flex-wrap:wrap;gap:8px}
.modal{display:none;position:fixed;inset:0;background:rgba(15,23,42,.55);backdrop-filter:blur(4px);z-index:100;align-items:center;justify-content:center;padding:16px;animation:fade .15s}
.modal.show{display:flex}
@keyframes fade{from{opacity:0}}
.modal .box{background:var(--card);border-radius:18px;padding:24px;width:100%;max-width:520px;max-height:90vh;overflow-y:auto;box-shadow:0 25px 50px -12px rgb(0 0 0 / .5);animation:pop .2s}
@keyframes pop{from{transform:scale(.96);opacity:0}}
.modal h3{margin:0 0 4px;font-size:20px;font-weight:800;letter-spacing:-.02em}
.modal .sub{margin:0 0 16px;color:var(--mut);font-size:13.5px}
.field{margin-top:14px}
.field label{display:block;font-size:13px;font-weight:600;margin-bottom:6px}
.field input,.field select{width:100%;padding:11px 13px;border:1px solid var(--bd);border-radius:10px;background:var(--bg);color:var(--fg);font:inherit;transition:border-color .15s,box-shadow .15s}
.field input:focus,.field select:focus{outline:none;border-color:var(--acc);box-shadow:0 0 0 3px rgb(37 99 235 / .15)}
.field small{display:block;color:var(--mut);font-size:12px;margin-top:4px}
.row{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media(max-width:480px){.row{grid-template-columns:1fr}}
hr.sep{border:none;border-top:1px solid var(--bd);margin:20px 0 0}
.err-msg{background:var(--down-bg);color:var(--down);padding:10px 14px;border-radius:10px;font-size:13.5px;margin-top:12px;display:none;border:1px solid rgba(220,38,38,.2)}
.err-msg.show{display:block}
.modal .foot{display:flex;gap:8px;justify-content:flex-end;margin-top:20px;flex-wrap:wrap}
#toasts{position:fixed;bottom:20px;right:20px;z-index:200;display:flex;flex-direction:column;gap:8px;max-width:340px}
.toast{background:var(--card);border:1px solid var(--bd);border-radius:12px;padding:12px 16px;box-shadow:var(--sh-lg);font-size:14px;animation:slidein .25s;display:flex;align-items:center;gap:10px;border-left:4px solid var(--acc)}
.toast.ok{border-left-color:var(--up)}
.toast.err{border-left-color:var(--down)}
.toast .ic{font-size:18px}
@keyframes slidein{from{transform:translateX(30px);opacity:0}}
.spinner{display:inline-block;width:14px;height:14px;border:2px solid var(--bd);border-top-color:var(--acc);border-radius:50%;animation:spin .8s linear infinite;vertical-align:middle}
@keyframes spin{to{transform:rotate(360deg)}}
@media(max-width:520px){
  .wrap{padding:14px}
  header.top{flex-direction:column;align-items:flex-start}
  .sum{grid-template-columns:repeat(2,1fr)}
  .card-actions button span.txt{display:none}
  .card-actions button{padding:8px 10px}
}
</style></head><body>
<div class="wrap">
<header class="top">
<h1 class="brand"><span class="logo">📡</span>Uptimer</h1>
<div class="actions">
<button class="pri" id="add" title="Thêm monitor (phím N)">+ Thêm</button>
<button class="icon" id="cfg" title="Cài đặt">⚙️</button>
<a href="/status" target="_blank" class="btn icon" title="Trang status công khai">🌐</a>
<a href="/logout" class="btn icon" title="Đăng xuất">↪</a>
</div>
</header>
<div class="sum" id="sum"></div>
<div id="list"></div>
<footer class="bar">
<span id="upd">Đang tải…</span>
<span><span class="spinner" id="sp" style="display:none"></span></span>
</footer>
</div>

<div class="modal" id="formModal">
<div class="box">
<h3 id="f_title">Thêm monitor</h3>
<p class="sub">Cấu hình URL, chu kỳ kiểm tra và điều kiện thành công.</p>
<div class="field"><label>Tên hiển thị</label><input id="f_name" placeholder="Ví dụ: Website chính"></div>
<div class="row">
  <div class="field"><label>Loại</label>
    <select id="f_type">
      <option value="http">HTTP(s)</option>
      <option value="keyword">HTTP + từ khoá</option>
      <option value="tcp">TCP port</option>
    </select>
  </div>
  <div class="field"><label>Chu kỳ (giây, ≥30)</label><input id="f_int" type="number" min="30" value="300"></div>
</div>
<div class="field"><label id="f_url_l">URL</label><input id="f_url" placeholder="https://example.com"></div>
<div class="field" id="f_kwbox"><label>Từ khoá phải xuất hiện trong nội dung</label><input id="f_kw" placeholder="Ví dụ: Welcome"></div>
<div class="row" id="f_httpbox">
  <div class="field"><label>Phương thức</label><select id="f_method"><option>GET</option><option>HEAD</option></select></div>
  <div class="field"><label>Mã HTTP hợp lệ</label><input id="f_exp" value="200-399" placeholder="200-399"></div>
</div>
<div class="row">
  <div class="field"><label>Timeout (giây)</label><input id="f_to" type="number" min="1" max="120" value="30"></div>
  <div class="field"><label>Thử lại trước khi DOWN</label><input id="f_ret" type="number" min="1" max="10" value="2"></div>
</div>
<div class="err-msg" id="f_err"></div>
<div class="foot">
  <button id="f_cancel">Huỷ</button>
  <button class="pri" id="f_save">Lưu monitor</button>
</div>
</div>
</div>

<div class="modal" id="cfgModal">
<div class="box">
<h3>Cài đặt</h3>
<p class="sub">Kênh cảnh báo và mật khẩu quản trị.</p>
<div class="field"><label>Tiêu đề trang status công khai</label><input id="c_title" placeholder="Trạng thái hệ thống"></div>
<div class="field"><label>Webhook (POST JSON)</label><input id="c_web" placeholder="https://..."><small>Nhận sự kiện UP/DOWN dạng JSON</small></div>
<div class="field"><label>Discord webhook URL</label><input id="c_dis" placeholder="https://discord.com/api/webhooks/..."></div>
<div class="row">
  <div class="field"><label>Telegram bot token</label><input id="c_tgt" placeholder="123:ABC..."></div>
  <div class="field"><label>Telegram chat id</label><input id="c_tgc" placeholder="-100..."></div>
</div>
<hr class="sep">
<div class="field"><label>Mật khẩu mới</label><input id="c_pass" type="password" placeholder="Để trống nếu không đổi" autocomplete="new-password"><small>Tối thiểu 4 ký tự. Đổi mật khẩu sẽ đăng xuất mọi phiên.</small></div>
<div class="field"><label>Xác nhận mật khẩu mới</label><input id="c_pass2" type="password" autocomplete="new-password"></div>
<div class="err-msg" id="c_err"></div>
<div class="foot">
  <button id="c_test">📨 Gửi thử</button>
  <button id="c_close">Đóng</button>
  <button class="pri" id="c_save">Lưu thay đổi</button>
</div>
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
  el.innerHTML='<span class="ic">'+(type==='err'?'⚠️':'✅')+'</span><span>'+esc(msg)+'</span>';
  $('toasts').appendChild(el);
  setTimeout(function(){el.style.transition='opacity .3s,transform .3s';el.style.opacity='0';el.style.transform='translateX(20px)';setTimeout(function(){el.remove();},300);},3200);
}
function dur(ms){
  var s=Math.round(ms/1000);
  if(s<60)return s+' giây';
  var m=Math.floor(s/60);
  if(m<60)return m+' phút';
  var h=Math.floor(m/60);
  if(h<48)return h+' giờ'+(m%60?' '+(m%60)+' phút':'');
  var d=Math.floor(h/24);
  return d+' ngày'+(h%24?' '+(h%24)+' giờ':'');
}
function ago(t){return t?dur(Date.now()-t)+' trước':'—';}
function pc(x){if(x<0)return '—';if(x>=99.995)return '100%';return x.toFixed(x>=99?2:1)+'%';}
function fmtMs(ms){if(!ms)return '—';if(ms<1000)return ms+' ms';return (ms/1000).toFixed(2)+' s';}
function sparkline(pts,w,h){
  if(!pts||!pts.length)return '<div style="height:'+h+'px;display:flex;align-items:center;justify-content:center;color:var(--mut);font-size:12px">Chưa có dữ liệu</div>';
  var max=1;pts.forEach(function(p){if(p.up&&p.ms>max)max=p.ms;});
  var n=pts.length,dx=n>1?w/(n-1):0,d='',marks='',brk=true;
  pts.forEach(function(p,i){
    var x=i*dx;
    if(p.up){var y=h-3-(p.ms/max)*(h-8);d+=(brk?'M':'L')+x.toFixed(1)+' '+y.toFixed(1)+' ';brk=false;}
    else{marks+='<rect x="'+(x-1.5).toFixed(1)+'" y="0" width="3" height="'+h+'" fill="var(--down)" opacity=".5" rx="1"/>';brk=true;}
  });
  return '<svg viewBox="0 0 '+w+' '+h+'" width="100%" height="'+h+'" preserveAspectRatio="none">'+marks+'<path d="'+d+'" fill="none" stroke="var(--acc)" stroke-width="1.5" stroke-linejoin="round" stroke-linecap="round"/></svg>';
}
function dayBar(days){
  return '<div class="days">'+days.map(function(d){
    var c=d.pct<0?'var(--pause)':d.pct>=99.9?'var(--up)':d.pct>=95?'var(--pend)':'var(--down)';
    return '<i title="'+esc(d.date)+': '+pc(d.pct)+'" style="background:'+c+'"></i>';
  }).join('')+'</div>';
}
var cache=[],open={},detail={},editId=null,checking={};
var LABEL={up:'UP',down:'DOWN',pending:'CHỜ',paused:'DỪNG'};

// cardInner = toàn bộ nội dung thay đổi được, KHÔNG chứa panel chi tiết
function cardInner(m){
  var st=m.status;
  var cert='';
  if(m.certExpiry){
    var dd=Math.floor((m.certExpiry-Date.now())/86400000);
    var cls=dd<14?' danger':dd<30?' warn':'';
    cert='<div class="m'+cls+'"><span>SSL còn</span><b>'+dd+' ngày</b></div>';
  }
  var lastErr=m.last&&!m.last.up?'<div class="m danger"><span>Lỗi gần nhất</span><b style="font-size:13px">'+esc(m.last.err||'lỗi')+'</b></div>':'';
  return '<div class="card-head">'+
      '<span class="dot '+st+'"></span>'+
      '<div class="card-title"><h3>'+esc(m.name)+'</h3><a class="url" href="'+esc(m.url)+'" target="_blank" rel="noopener">'+esc(m.url)+'</a></div>'+
      '<span class="badge '+st+'">'+LABEL[st]+'</span>'+
    '</div>'+
    '<div class="metrics">'+
      '<div class="m"><span>24 giờ</span><b>'+pc(m.up24)+'</b></div>'+
      '<div class="m"><span>7 ngày</span><b>'+pc(m.up7)+'</b></div>'+
      '<div class="m"><span>30 ngày</span><b>'+pc(m.up30)+'</b></div>'+
      '<div class="m"><span>TB</span><b>'+fmtMs(m.avgMs)+'</b></div>'+
      cert+lastErr+
    '</div>'+
    '<div class="chart">'+sparkline(m.spark,360,32)+'</div>'+
    dayBar(m.days)+
    '<div class="metrics" style="margin:10px 0 0;font-size:12.5px">'+
      '<div class="m"><span>Kiểm tra</span><b style="font-size:13px">'+ago(m.last&&m.last.t)+'</b></div>'+
      '<div class="m"><span>Trạng thái từ</span><b style="font-size:13px">'+ago(m.since)+'</b></div>'+
      '<div class="m"><span>Chu kỳ</span><b style="font-size:13px">'+m.interval+'s</b></div>'+
    '</div>'+
    '<div class="card-actions">'+
      '<button data-a="detail" data-id="'+m.id+'">'+(open[m.id]?'▴':'▾')+'<span class="txt">Chi tiết</span></button>'+
      '<button data-a="check" data-id="'+m.id+'"'+(checking[m.id]?' disabled':'')+'>'+(checking[m.id]?'<span class="spinner"></span>':'↻')+'<span class="txt">Check ngay</span></button>'+
      '<button data-a="'+(m.paused?'resume':'pause')+'" data-id="'+m.id+'">'+(m.paused?'▶':'⏸')+'<span class="txt">'+(m.paused?'Tiếp tục':'Tạm dừng')+'</span></button>'+
      '<button data-a="edit" data-id="'+m.id+'">✎<span class="txt">Sửa</span></button>'+
      '<button class="dng" data-a="del" data-id="'+m.id+'">🗑<span class="txt">Xoá</span></button>'+
    '</div>';
}

// card = <article> đầy đủ, chỉ dùng khi tạo mới
function card(m){
  return '<article class="card" id="card-'+m.id+'" data-status="'+m.status+'">'+
    '<div class="body">'+cardInner(m)+'</div>'+
    '<div class="d-slot" id="d_'+m.id+'">'+(open[m.id]&&detail[m.id]?detail[m.id]:'')+'</div>'+
  '</article>';
}

function detailHTML(d){
  var h='<div class="detail"><h4>Thời gian phản hồi 24 giờ qua</h4>';
  h+=d.series&&d.series.length?sparkline(d.series,680,80):'<div style="color:var(--mut);font-size:13px">Chưa có dữ liệu.</div>';
  h+='<h4 style="margin-top:16px">Sự cố gần đây</h4>';
  if(!d.incidents||!d.incidents.length){
    h+='<div style="color:var(--mut);font-size:13px">Chưa có sự cố nào 🎉</div>';
  } else {
    h+='<table>'+d.incidents.map(function(i){
      return '<tr><td style="white-space:nowrap;color:var(--mut)">'+new Date(i.start).toLocaleString('vi-VN')+'</td>'+
        '<td style="white-space:nowrap">'+(i.end?dur(i.end-i.start):'<b style="color:var(--down)">đang diễn ra</b>')+'</td>'+
        '<td>'+esc(i.reason)+'</td></tr>';
    }).join('')+'</table>';
  }
  return h+'</div>';
}

// render cập nhật tại chỗ — KHÔNG đụng vào các <article> đã có
function render(ms){
  var c={up:0,down:0,paused:0,pending:0};
  ms.forEach(function(m){c[m.status]=(c[m.status]||0)+1;});
  var sumHTML=
    '<div class="stat up"><div class="stat-val">'+c.up+'</div><div class="stat-lbl">Hoạt động</div></div>'+
    '<div class="stat down"><div class="stat-val">'+c.down+'</div><div class="stat-lbl">Sự cố</div></div>'+
    '<div class="stat"><div class="stat-val" style="color:var(--pause)">'+c.paused+'</div><div class="stat-lbl">Tạm dừng</div></div>'+
    (c.pending?'<div class="stat pend"><div class="stat-val">'+c.pending+'</div><div class="stat-lbl">Đang chờ</div></div>':'');
  var sumEl=$('sum');
  if(sumEl.dataset.sig!==sumHTML){sumEl.innerHTML=sumHTML;sumEl.dataset.sig=sumHTML;}

  var list=$('list');
  if(!ms.length){
    if(!list.querySelector('.empty')){
      list.innerHTML='<div class="empty"><div class="empty-icon">📡</div><h3>Chưa có monitor nào</h3><p>Bấm <b>+ Thêm</b> để bắt đầu giám sát website, API hoặc TCP port.</p></div>';
    }
    return;
  }
  // xoá placeholder nếu có
  var ph=list.querySelector('.empty');
  if(ph)ph.remove();

  // gom các <article> hiện có theo id
  var existing={};
  list.querySelectorAll('article.card').forEach(function(el){
    var id=el.id.replace(/^card-/,'');
    if(id)existing[id]=el;
  });

  ms.forEach(function(m){
    var el=existing[m.id];
    if(!el){
      // tạo mới — animation rise chạy 1 lần
      var tmp=document.createElement('div');
      tmp.innerHTML=card(m);
      list.appendChild(tmp.firstElementChild);
    } else {
      // cập nhật tại chỗ: chỉ đổi thuộc tính + .body, KHÔNG đụng detail
      if(el.dataset.status!==m.status)el.dataset.status=m.status;
      if(!checking[m.id]){
        var body=el.querySelector('.body');
        if(body)body.innerHTML=cardInner(m);
      }
      // dọn card bị xoá xong sẽ xử lý bên dưới
    }
    delete existing[m.id];
  });

  // xoá các thẻ không còn trong danh sách
  Object.keys(existing).forEach(function(id){existing[id].remove();});
}

function loadDetail(id){
  api('GET','/api/monitors/'+id).then(function(d){
    var h=detailHTML(d);
    if(detail[id]===h)return; // không đổi thì thôi
    detail[id]=h;
    var el=$('d_'+id);
    if(el&&open[id])el.innerHTML=h;
  }).catch(function(){});
}
function load(){
  $('sp').style.display='inline-block';
  api('GET','/api/monitors').then(function(ms){
    cache=ms;render(ms);$('sp').style.display='none';
    $('upd').textContent='Cập nhật: '+new Date().toLocaleTimeString('vi-VN');
    Object.keys(open).forEach(function(id){if(open[id])loadDetail(id);});
  }).catch(function(e){
    $('sp').style.display='none';
    $('list').innerHTML='<div class="empty"><div class="empty-icon">⚠️</div><h3>Lỗi tải dữ liệu</h3><p>'+esc(e.message)+'</p></div>';
  });
}

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
$('f_type').onchange=fsync;
$('add').onclick=function(){openForm(null);};
$('f_cancel').onclick=closeForm;
$('f_save').onclick=saveForm;

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
$('cfg').onclick=openCfg;
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

$('list').onclick=function(e){
  var b=e.target.closest('button');
  if(!b)return;
  var id=b.getAttribute('data-id'),a=b.getAttribute('data-a');
  if(!id||!a)return;
  if(a==='detail'){
    open[id]=!open[id];
    if(open[id])loadDetail(id);
    else{var d=$('d_'+id);if(d)d.innerHTML='';}
    render(cache); // cập nhật mũi tên ▾/▴ không chớp
  }
  else if(a==='edit'){cache.forEach(function(m){if(m.id===id)openForm(m);});}
  else if(a==='del'){
    if(confirm('Xoá monitor này và toàn bộ lịch sử?')){
      api('DELETE','/api/monitors/'+id).then(function(){toast('Đã xoá');load();}).catch(function(e){toast(e.message,'err');});
    }
  } else if(a==='check'){
    if(checking[id])return;
    checking[id]=true;
    // cập nhật riêng nút hiện tại, không render lại cả card
    b.disabled=true;
    b.innerHTML='<span class="spinner"></span><span class="txt">Check ngay</span>';
    api('POST','/api/monitors/'+id+'/check')
      .then(function(){delete checking[id];toast('Đã kiểm tra');load();})
      .catch(function(){delete checking[id];load();});
  } else {
    api('POST','/api/monitors/'+id+'/'+a).then(function(){toast(a==='pause'?'Đã tạm dừng':'Đã tiếp tục');load();}).catch(function(e){toast(e.message,'err');});
  }
};

document.querySelectorAll('.modal').forEach(function(m){
  m.addEventListener('click',function(e){if(e.target===m)m.classList.remove('show');});
});
document.addEventListener('keydown',function(e){
  if(e.key==='Escape'){
    if($('formModal').classList.contains('show'))closeForm();
    if($('cfgModal').classList.contains('show'))closeCfg();
  }
  if((e.key==='n'||e.key==='N')&&!e.target.matches('input,select,textarea')&&!$('formModal').classList.contains('show')&&!$('cfgModal').classList.contains('show')){
    e.preventDefault();openForm(null);
  }
});
$('formModal').addEventListener('keydown',function(e){
  if(e.key==='Enter'&&e.target.tagName==='INPUT'){e.preventDefault();saveForm();}
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
:root{--bg:#f8fafc;--fg:#0f172a;--mut:#64748b;--card:#fff;--bd:#e2e8f0;--up:#16a34a;--down:#dc2626;--pend:#d97706;--pause:#94a3b8}
@media(prefers-color-scheme:dark){:root{--bg:#0b1220;--fg:#e2e8f0;--mut:#94a3b8;--card:#152033;--bd:#1e293b}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.55 system-ui,-apple-system,sans-serif;-webkit-font-smoothing:antialiased}
.wrap{max-width:760px;margin:0 auto;padding:24px 20px}
h1{font-size:24px;font-weight:800;letter-spacing:-.02em;margin:0 0 4px}
.sub{color:var(--mut);font-size:13.5px;margin-bottom:24px}
.banner{border-radius:16px;padding:20px 24px;color:#fff;font-weight:700;font-size:18px;background:linear-gradient(135deg,#16a34a,#15803d);box-shadow:0 10px 25px -5px rgb(22 163 74 / .4);display:flex;align-items:center;gap:12px;margin-bottom:20px;transition:background .3s}
.banner.down{background:linear-gradient(135deg,#dc2626,#b91c1c);box-shadow:0 10px 25px -5px rgb(220 38 38 / .4)}
.banner .ic{font-size:26px}
.card{background:var(--card);border:1px solid var(--bd);border-radius:14px;padding:18px;margin-bottom:10px;box-shadow:0 1px 3px rgb(0 0 0 / .08)}
.top{display:flex;justify-content:space-between;align-items:center;gap:12px;margin-bottom:12px}
.top h3{margin:0;font-size:15px;font-weight:700}
.st{font-weight:700;font-size:13px;padding:4px 10px;border-radius:8px;color:#fff;background:var(--pause)}
.st.up{background:var(--up)}.st.down{background:var(--down)}.st.pending{background:var(--pend)}
.days{display:flex;gap:2px;height:28px;margin-top:10px}
.days i{flex:1;border-radius:3px;transition:transform .15s}
.days i:hover{transform:scaleY(1.15)}
.meta{display:flex;justify-content:space-between;margin-top:10px;font-size:12.5px;color:var(--mut);flex-wrap:wrap;gap:6px}
.foot{text-align:center;color:var(--mut);font-size:12px;margin-top:24px}
</style></head><body><div class="wrap">
<h1 id="t">Trạng thái hệ thống</h1>
<p class="sub" id="sub">Đang tải dữ liệu…</p>
<div class="banner" id="b"><span class="ic">⏳</span><span>Đang tải…</span></div>
<div id="list"></div>
<p class="foot" id="upd"></p>
</div>
<script>
var $=function(i){return document.getElementById(i)};
function esc(s){return String(s==null?'':s).replace(/[&<>"']/g,function(c){return ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'})[c];});}
function pc(x){if(x<0)return '—';if(x>=99.995)return '100%';return x.toFixed(x>=99?2:1)+'%';}
var LABEL={up:'Hoạt động',down:'Sự cố',pending:'Đang chờ',paused:'Tạm dừng'};
var lastJSON='';

function renderCard(m){
  var bars=m.days.map(function(x){
    var c=x.pct<0?'var(--pause)':x.pct>=99.9?'var(--up)':x.pct>=95?'var(--pend)':'var(--down)';
    return '<i title="'+esc(x.date)+': '+pc(x.pct)+'" style="background:'+c+'"></i>';
  }).join('');
  var downFor=m.status==='down'&&m.since?'<span style="color:var(--down)">Sự cố '+Math.floor((Date.now()-m.since)/60000)+' phút</span>':'';
  return '<div class="top"><h3>'+esc(m.name)+'</h3><span class="st '+m.status+'">'+(LABEL[m.status]||m.status)+'</span></div>'+
    '<div class="days">'+bars+'</div>'+
    '<div class="meta"><span>Uptime 30 ngày: <b>'+pc(m.up30)+'</b></span>'+downFor+'</div>';
}

function render(d){
  var bad=d.overall==='down';
  // banner: chỉ đổi nếu state khác
  var b=$('b');
  var wantBad=bad?'1':'0';
  if(b.dataset.bad!==wantBad){
    b.className='banner'+(bad?' down':'');
    b.innerHTML='<span class="ic">'+(bad?'⚠️':'✅')+'</span><span>'+(bad?'Một số dịch vụ đang gặp sự cố':'Tất cả dịch vụ hoạt động bình thường')+'</span>';
    b.dataset.bad=wantBad;
  }
  $('sub').textContent=d.items.length+' dịch vụ được giám sát';

  var list=$('list');
  // xoá nếu danh sách rỗng
  if(!d.items.length){list.innerHTML='';return;}

  var existing={};
  list.querySelectorAll('.card').forEach(function(el){
    if(el.dataset.id)existing[el.dataset.id]=el;
  });

  // dùng index làm id tạm nếu item không có id
  d.items.forEach(function(m,idx){
    var key=m.name+'|'+idx;
    var html=renderCard(m);
    var el=existing[key];
    if(!el){
      var div=document.createElement('div');
      div.className='card';
      div.dataset.id=key;
      div.innerHTML=html;
      list.appendChild(div);
    } else if(el.innerHTML!==html){
      el.innerHTML=html;
    }
    delete existing[key];
  });
  Object.keys(existing).forEach(function(k){existing[k].remove();});
}

function load(){
  fetch('/status.json').then(function(r){return r.json();}).then(function(d){
    $('t').textContent=d.title;document.title=d.title;
    var j=JSON.stringify(d.items);
    // luôn update banner/sub (rẻ) nhưng bỏ qua list nếu items không đổi
    if(j!==lastJSON){
      lastJSON=j;
      render(d);
    } else {
      // vẫn cập nhật thời gian "Sự cố X phút" mà không rebuild
      document.querySelectorAll('.card').forEach(function(el,idx){
        var m=d.items[idx];if(!m)return;
        if(m.status==='down'&&m.since){
          var span=el.querySelector('.meta span:last-child');
          if(span)span.textContent='Sự cố '+Math.floor((Date.now()-m.since)/60000)+' phút';
        }
      });
    }
    $('upd').textContent='Cập nhật lúc '+new Date(d.time).toLocaleString('vi-VN');
  }).catch(function(){$('b').textContent='Không tải được dữ liệu';});
}
load();setInterval(load,30000);
</script></body></html>`
