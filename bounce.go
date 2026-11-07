// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"sort"
	"strings"
)

// A bouncer is a non-halting run whose tape is a fixed left wall, a block
// that is repeated one more time after each pass, and a fixed right wall.
// proveBouncer replays that pass on an abstract tape. The replay is uniform
// in the number of repetitions, so one successful pass is a proof for every
// larger copy count. A concrete check for a few copy counts guards the replay.

type aseg struct {
	wall bool
	s    string
	w    string
	a, b int
}

type conf struct {
	segs  []aseg
	state int
	si    int
	off   int
}

type bprover struct {
	e           *engine
	chainAlways bool
	absorbWalls bool
}

type prog struct {
	A, M, B string
	copies  int
}

func (e *engine) proveBouncer() (Outcome, bool) {
	type cand struct {
		walls, copies, side, st int
		A, M, B                 string
	}
	var cands []cand
	for side := 0; side < 2; side++ {
		for st := 0; st < e.n; st++ {
			progs := findProgs(e.recStrings(side, st))
			if len(progs) == 0 {
				continue
			}
			best := progs[0]
			for _, p := range progs[1:] {
				if len(p.A)+len(p.B) < len(best.A)+len(best.B) ||
					(len(p.A)+len(p.B) == len(best.A)+len(best.B) && p.copies > best.copies) {
					best = p
				}
			}
			cands = append(cands, cand{
				walls: len(best.A) + len(best.B), copies: best.copies,
				side: side, st: st, A: best.A, M: best.M, B: best.B,
			})
		}
	}
	sort.Slice(cands, func(i, j int) bool {
		if cands[i].walls != cands[j].walls {
			return cands[i].walls < cands[j].walls
		}
		return cands[i].copies > cands[j].copies
	})
	type mode struct{ norm, always, absorb bool }
	modes := []mode{
		{false, false, false},
		{true, true, true},
		{true, true, false},
		{false, true, true},
	}
	for _, c := range cands {
		for _, j0 := range []int{2, 3, 4, 6, 8, 12} {
			if j0 > c.copies-1 {
				break
			}
			for _, m := range modes {
				if !proveFrom(e, c.A, c.M, c.B, j0, c.side, c.st, m.norm, m.always, m.absorb) {
					continue
				}
				ok := true
				for _, K := range []int{0, 1, 2, 4} {
					capn := 2000 * (len(c.A) + len(c.B) + len(c.M)*(j0+K+1) + 2)
					if !e.concretePeriod(c.A, c.M, c.B, j0+K, c.side, c.st, capn) {
						ok = false
						break
					}
				}
				if !ok {
					continue
				}
				o := e.finish(VerdictLoop, ReasonBounce, c.st)
				o.Offset = len(c.M)
				if c.side == 0 {
					o.Side = "right"
				} else {
					o.Side = "left"
				}
				return o, true
			}
		}
	}
	return Outcome{}, false
}

func (e *engine) recStrings(side, state int) []string {
	n := e.rn[side][state]
	if n > 80 {
		n = 80
	}
	rs := e.recs[side][state]
	if n > len(rs) {
		n = len(rs)
	}
	out := make([]string, n)
	for i := 0; i < n; i++ {
		out[i] = recString(rs[i])
	}
	return out
}

func recString(r rec) string {
	b := make([]byte, r.n)
	for i := 0; i < int(r.n); i++ {
		if r.b[i>>6]&(1<<uint(i&63)) != 0 {
			b[i] = '1'
		} else {
			b[i] = '0'
		}
	}
	return string(b)
}

func findProgs(recs []string) []prog {
	var out []prog
	for s := 0; s+2 < len(recs); s++ {
		a, b := recs[s], recs[s+1]
		d := len(b) - len(a)
		if d <= 0 || len(recs[s+2])-len(b) != d {
			continue
		}
		p := -1
		var M string
		for i := 0; i <= len(a); i++ {
			if i+d > len(b) {
				continue
			}
			M = b[i : i+d]
			if M != "" && a[:i]+M+a[i:] == b && b[:i]+M+b[i:] == recs[s+2] {
				p = i
				break
			}
		}
		if p < 0 {
			continue
		}
		A, B := a[:p], a[p:]
		j := 0
		for s+j < len(recs) && recs[s+j] == A+strings.Repeat(M, j)+B {
			j++
		}
		if j >= 3 {
			out = append(out, prog{A: A, M: M, B: B, copies: j})
		}
	}
	return out
}

func primitive(w string, a, b int) (string, int, int) {
	if w == "" {
		return w, a, b
	}
	for L := 1; L < len(w); L++ {
		if len(w)%L == 0 && w == strings.Repeat(w[:L], len(w)/L) {
			m := len(w) / L
			return w[:L], a * m, b * m
		}
	}
	return w, a, b
}

func proveFrom(e *engine, A, M, B string, j0, side, q int, normalize, chainAlways, absorbWalls bool) bool {
	if j0 < 1 || M == "" {
		return false
	}
	w, ca, cb := M, j0, 1
	if normalize {
		w, ca, cb = primitive(M, j0, 1)
	}
	if ca < 1 {
		return false
	}
	var segs []aseg
	if A != "" {
		segs = append(segs, aseg{wall: true, s: A})
	}
	segs = append(segs, aseg{w: w, a: ca, b: cb})
	if B != "" {
		segs = append(segs, aseg{wall: true, s: B})
	}
	c := &conf{segs: segs, state: q}
	if side == 1 {
		c.si, c.off = 0, 0
	} else {
		c.si = len(segs) - 1
		if segs[c.si].wall {
			c.off = len(segs[c.si].s) - 1
		} else {
			c.off = -1
		}
	}
	var goal []aseg
	if A != "" {
		goal = append(goal, aseg{wall: true, s: A})
	}
	goal = append(goal, aseg{w: M, a: j0 + 1, b: 1})
	if B != "" {
		goal = append(goal, aseg{wall: true, s: B})
	}
	p := &bprover{e: e, chainAlways: chainAlways, absorbWalls: absorbWalls}
	seen := map[string]bool{}
	startLen := len(A) + len(B) + len(M)*j0
	for range 8000 {
		if minLen(c) > startLen+4*len(M)+8 {
			return false
		}
		if c.state == q && tapesEqual(c.segs, goal) {
			if side == 1 && headOnLeft(c) || side == 0 && headOnRight(c) {
				return true
			}
		}
		sig := c.signature()
		if seen[sig] {
			return false
		}
		seen[sig] = true
		if !p.step(c) {
			return false
		}
	}
	return false
}

func minLen(c *conf) int {
	n := 0
	for _, s := range c.segs {
		if s.wall {
			n += len(s.s)
		} else {
			n += len(s.w) * s.a
		}
	}
	return n
}

func headOnLeft(c *conf) bool { return c.si == 0 && c.off == 0 }

func headOnRight(c *conf) bool {
	if len(c.segs) == 0 || c.si != len(c.segs)-1 {
		return false
	}
	seg := c.segs[c.si]
	if seg.wall {
		return c.off == len(seg.s)-1
	}
	return c.off == -1
}

func (c *conf) signature() string {
	var b strings.Builder
	fmt.Fprintf(&b, "%d|%d|%d|", c.state, c.si, c.off)
	for _, s := range c.segs {
		if s.wall {
			b.WriteByte('W')
			b.WriteString(s.s)
			b.WriteByte(';')
		} else {
			fmt.Fprintf(&b, "R%s,%d,%d;", s.w, s.a, s.b)
		}
	}
	return b.String()
}

func (p *bprover) step(c *conf) bool {
	if p.absorbWalls {
		absorb(c)
	}
	if c.si < 0 || c.si >= len(c.segs) {
		return false
	}
	if c.segs[c.si].wall {
		return p.micro(c)
	}
	if c.off != 0 && c.off != -1 {
		return false
	}
	try := p.chainAlways
	if !try {
		word := c.segs[c.si].w
		if word == "" {
			return false
		}
		sym := word[0]
		if c.off == -1 {
			sym = word[len(word)-1]
		}
		tr, ok := p.trans(c.state, sym)
		if !ok {
			return false
		}
		try = (c.off == 0 && tr.Dir == 1) || (c.off == -1 && tr.Dir == -1)
	}
	if try && p.tryChain(c) {
		return true
	}
	return p.peel(c)
}

func (p *bprover) trans(state int, sym byte) (Trans, bool) {
	if state < 0 || state >= p.e.n || (sym != '0' && sym != '1') {
		return Trans{}, false
	}
	bit := 0
	if sym == '1' {
		bit = 1
	}
	if !p.e.def[state][bit] {
		return Trans{}, false
	}
	t := p.e.tr[state][bit]
	if t.Next < 0 {
		return Trans{}, false
	}
	return t, true
}

func absorb(c *conf) {
	changed := true
	for changed {
		changed = false
		for i := 0; i < len(c.segs)-1; {
			left, right := c.segs[i], c.segs[i+1]
			if left.wall && !right.wall && right.w != "" && left.s != "" &&
				len(left.s)%len(right.w) == 0 &&
				left.s == strings.Repeat(right.w, len(left.s)/len(right.w)) &&
				c.si != i {
				c.segs[i+1].a += len(left.s) / len(right.w)
				deleteSeg(c, i)
				if c.si > i {
					c.si--
				}
				changed = true
				continue
			}
			if !left.wall && right.wall && left.w != "" && right.s != "" &&
				len(right.s)%len(left.w) == 0 &&
				right.s == strings.Repeat(left.w, len(right.s)/len(left.w)) &&
				!(c.si == i+1 || (c.si == i && c.off == -1)) {
				c.segs[i].a += len(right.s) / len(left.w)
				deleteSeg(c, i+1)
				if c.si > i+1 {
					c.si--
				}
				changed = true
				continue
			}
			i++
		}
	}
}

func (p *bprover) micro(c *conf) bool {
	if !c.segs[c.si].wall || c.off < 0 || c.off >= len(c.segs[c.si].s) {
		return false
	}
	sym := c.segs[c.si].s[c.off]
	tr, ok := p.trans(c.state, sym)
	if !ok {
		return false
	}
	bs := []byte(c.segs[c.si].s)
	bs[c.off] = '0' + tr.Write
	c.segs[c.si].s = string(bs)
	c.state = int(tr.Next)
	n := len(c.segs[c.si].s)
	c.off += int(tr.Dir)
	if c.off >= 0 && c.off < n {
		return mergeWalls(c)
	}
	if c.off == -1 {
		if !movePrev(c) {
			return false
		}
	} else if c.off == n {
		if !moveNext(c) {
			return false
		}
	} else {
		return false
	}
	return mergeWalls(c)
}

func movePrev(c *conf) bool {
	if c.si == 0 {
		insertSeg(c, 0, aseg{wall: true, s: "0"})
		c.off = 0
		return true
	}
	c.si--
	prev := c.segs[c.si]
	if prev.wall {
		if prev.s == "" {
			return false
		}
		c.off = len(prev.s) - 1
		return true
	}
	c.off = -1
	return true
}

func moveNext(c *conf) bool {
	if c.si == len(c.segs)-1 {
		c.segs = append(c.segs, aseg{wall: true, s: "0"})
		c.si++
		c.off = 0
		return true
	}
	c.si++
	nxt := c.segs[c.si]
	if nxt.wall && nxt.s == "" {
		return false
	}
	c.off = 0
	return true
}

func mergeWalls(c *conf) bool {
	if len(c.segs) == 0 {
		return false
	}
	out := make([]aseg, 0, len(c.segs))
	newSI, newOff := 0, c.off
	placed := false
	for i, s := range c.segs {
		if s.wall && s.s == "" {
			if c.si == i {
				return false
			}
			continue
		}
		if s.wall && len(out) > 0 && out[len(out)-1].wall {
			if c.si == i {
				newOff = len(out[len(out)-1].s) + c.off
				newSI = len(out) - 1
				placed = true
			}
			out[len(out)-1].s += s.s
			continue
		}
		if c.si == i {
			newSI = len(out)
			newOff = c.off
			placed = true
		}
		out = append(out, s)
	}
	if len(out) == 0 || !placed {
		return false
	}
	c.segs = out
	c.si = newSI
	c.off = newOff
	return c.si >= 0 && c.si < len(c.segs)
}

func (p *bprover) peel(c *conf) bool {
	if c.si < 0 || c.si >= len(c.segs) || c.segs[c.si].wall {
		return false
	}
	seg := c.segs[c.si]
	if seg.a < 1 {
		return false
	}
	if seg.a == 1 && seg.b == 0 {
		c.segs[c.si] = aseg{wall: true, s: seg.w}
		if c.off == -1 {
			c.off = len(seg.w) - 1
		} else {
			c.off = 0
		}
		return true
	}
	if seg.a == 1 && seg.b > 0 {
		return false
	}
	word := seg.w
	c.segs[c.si].a--
	if c.off == 0 {
		insertSeg(c, c.si, aseg{wall: true, s: word})
		c.off = 0
		return true
	}
	insertSeg(c, c.si+1, aseg{wall: true, s: word})
	c.si++
	c.off = len(word) - 1
	return true
}

func insertSeg(c *conf, i int, s aseg) {
	c.segs = append(c.segs, aseg{})
	copy(c.segs[i+1:], c.segs[i:])
	c.segs[i] = s
}

func deleteSeg(c *conf, i int) {
	c.segs = append(c.segs[:i], c.segs[i+1:]...)
}

func (p *bprover) tryChain(c *conf) bool {
	if c.si < 0 || c.si >= len(c.segs) {
		return false
	}
	seg := c.segs[c.si]
	if seg.wall || seg.a < 1 || seg.w == "" {
		return false
	}
	if c.off == 0 {
		return p.chainRight(c)
	}
	if c.off == -1 {
		return p.chainLeft(c)
	}
	return false
}

func (p *bprover) chainRight(c *conf) bool {
	word := c.segs[c.si].w
	leftS := ""
	if c.si > 0 && c.segs[c.si-1].wall {
		leftS = c.segs[c.si-1].s
	}
	for blen := 0; blen <= len(leftS); blen++ {
		buf := ""
		if blen > 0 {
			buf = leftS[len(leftS)-blen:]
		}
		word2, ok := p.simChainRight(c.state, buf, word)
		if !ok {
			continue
		}
		if blen > 0 {
			c.segs[c.si-1].s = leftS[:len(leftS)-blen]
			if c.segs[c.si-1].s == "" {
				deleteSeg(c, c.si-1)
				c.si--
			}
		}
		c.segs[c.si].w = word2
		return placeBufRight(c, buf)
	}
	return false
}

func placeBufRight(c *conf, buf string) bool {
	segI := c.si
	if segI == len(c.segs)-1 {
		c.segs = append(c.segs, aseg{wall: true, s: buf + "0"})
		c.si = segI + 1
		c.off = len(buf)
		return true
	}
	if c.segs[segI+1].wall {
		c.segs[segI+1].s = buf + c.segs[segI+1].s
		c.si = segI + 1
		c.off = len(buf)
		return c.off < len(c.segs[c.si].s)
	}
	if buf != "" {
		insertSeg(c, segI+1, aseg{wall: true, s: buf})
		c.si = segI + 2
	} else {
		c.si = segI + 1
	}
	c.off = 0
	return true
}

func (p *bprover) simChainRight(state int, buf, word string) (string, bool) {
	region := []byte(buf + word)
	pos := len(buf)
	start := state
	seen := map[string]bool{}
	limit := (len(region)+2)*(p.e.n+2)*6 + 4
	for range limit {
		if pos == len(region) {
			if state != start {
				return "", false
			}
			gotWord := string(region[:len(word)])
			gotBuf := string(region[len(word):])
			if gotBuf != buf || len(gotWord) != len(word) {
				return "", false
			}
			return gotWord, true
		}
		if pos < 0 || pos >= len(region) {
			return "", false
		}
		tr, ok := p.trans(state, region[pos])
		if !ok {
			return "", false
		}
		region[pos] = '0' + tr.Write
		pos += int(tr.Dir)
		state = int(tr.Next)
		key := fmt.Sprintf("%d,%d,%s", state, pos, region)
		if seen[key] {
			return "", false
		}
		seen[key] = true
	}
	return "", false
}

func (p *bprover) chainLeft(c *conf) bool {
	word := c.segs[c.si].w
	rightS := ""
	if c.si+1 < len(c.segs) && c.segs[c.si+1].wall {
		rightS = c.segs[c.si+1].s
	}
	for blen := 0; blen <= len(rightS); blen++ {
		buf := ""
		if blen > 0 {
			buf = rightS[:blen]
		}
		word2, ok := p.simChainLeft(c.state, buf, word)
		if !ok {
			continue
		}
		if blen > 0 {
			c.segs[c.si+1].s = rightS[blen:]
			if c.segs[c.si+1].s == "" {
				deleteSeg(c, c.si+1)
			}
		}
		c.segs[c.si].w = word2
		return placeBufLeft(c, buf)
	}
	return false
}

func placeBufLeft(c *conf, buf string) bool {
	segI := c.si
	if segI == 0 {
		insertSeg(c, 0, aseg{wall: true, s: "0" + buf})
		c.si = 0
		c.off = 0
		return true
	}
	if c.segs[segI-1].wall {
		c.segs[segI-1].s += buf
		c.si = segI - 1
		c.off = len(c.segs[c.si].s) - len(buf) - 1
		return c.off >= 0
	}
	if buf != "" {
		insertSeg(c, segI, aseg{wall: true, s: buf})
	}
	c.si = segI - 1
	c.off = -1
	return true
}

func (p *bprover) simChainLeft(state int, buf, word string) (string, bool) {
	if word == "" {
		return "", false
	}
	region := []byte(word + buf)
	pos := len(word) - 1
	start := state
	seen := map[string]bool{}
	limit := (len(region)+2)*(p.e.n+2)*6 + 4
	for range limit {
		if pos == -1 {
			if state != start {
				return "", false
			}
			gotBuf := string(region[:len(buf)])
			gotWord := string(region[len(buf):])
			if gotBuf != buf || len(gotWord) != len(word) {
				return "", false
			}
			return gotWord, true
		}
		if pos < 0 || pos >= len(region) {
			return "", false
		}
		tr, ok := p.trans(state, region[pos])
		if !ok {
			return "", false
		}
		region[pos] = '0' + tr.Write
		pos += int(tr.Dir)
		state = int(tr.Next)
		key := fmt.Sprintf("%d,%d,%s", state, pos, region)
		if seen[key] {
			return "", false
		}
		seen[key] = true
	}
	return "", false
}

func (e *engine) concretePeriod(A, M, B string, copies, side, q, cap int) bool {
	s := A + strings.Repeat(M, copies) + B
	if s == "" {
		return false
	}
	tape := map[int]byte{}
	for i := 0; i < len(s); i++ {
		if s[i] == '1' {
			tape[i] = 1
		}
	}
	head := len(s) - 1
	if side == 1 {
		head = 0
	}
	state := q
	goal := A + strings.Repeat(M, copies+1) + B
	for range cap {
		if state < 0 || state >= e.n {
			return false
		}
		sym := tape[head]
		if !e.def[state][sym] || e.tr[state][sym].Next < 0 {
			return false
		}
		tr := e.tr[state][sym]
		if tr.Write == 0 {
			delete(tape, head)
		} else {
			tape[head] = 1
		}
		head += int(tr.Dir)
		state = int(tr.Next)
		if state == q && headMatches(tape, head, goal, side) {
			return true
		}
	}
	return false
}

func headMatches(tape map[int]byte, head int, goal string, side int) bool {
	if goal == "" {
		return false
	}
	start := head
	if side != 1 {
		start = head - (len(goal) - 1)
	}
	for i := 0; i < len(goal); i++ {
		want := byte(0)
		if goal[i] == '1' {
			want = 1
		}
		if tape[start+i] != want {
			return false
		}
	}
	for pos, v := range tape {
		if v != 0 && (pos < start || pos >= start+len(goal)) {
			return false
		}
	}
	if side == 1 {
		return head == start
	}
	return head == start+len(goal)-1
}

type block struct {
	w    string
	a, b int
}

type form struct {
	L, w, R string
	a, b    int
}

func tapesEqual(x, y []aseg) bool {
	f1, ok1 := oneRep(x)
	f2, ok2 := oneRep(y)
	if !ok1 || !ok2 {
		c1, good1 := betterCanon(x)
		c2, good2 := betterCanon(y)
		return good1 && good2 && blocksEqual(c1, c2)
	}
	return formsEqual(f1, f2)
}

func blocksEqual(a, b []block) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

type oblock struct {
	rep  bool
	s    string
	a, b int
}

func oneRep(segs []aseg) (form, bool) {
	var blocks []oblock
	for _, s := range segs {
		if s.wall {
			if s.s != "" {
				blocks = append(blocks, oblock{s: s.s})
			}
			continue
		}
		if s.a < 1 || s.b < 0 || s.w == "" {
			return form{}, false
		}
		w, a, b := primitive(s.w, s.a, s.b)
		blocks = append(blocks, oblock{rep: true, s: w, a: a, b: b})
	}
	var merged []oblock
	for _, b := range blocks {
		if n := len(merged); n > 0 && !b.rep && !merged[n-1].rep {
			merged[n-1].s += b.s
			continue
		}
		if n := len(merged); n > 0 && b.rep && merged[n-1].rep && merged[n-1].s == b.s {
			merged[n-1].a += b.a
			merged[n-1].b += b.b
			continue
		}
		merged = append(merged, b)
	}
	reps := 0
	var rep oblock
	for _, b := range merged {
		if b.rep && b.b > 0 {
			reps++
			rep = b
		}
	}
	if reps > 1 {
		return form{}, false
	}
	if reps == 0 {
		var text strings.Builder
		for _, b := range merged {
			if b.rep {
				text.WriteString(strings.Repeat(b.s, b.a))
			} else {
				text.WriteString(b.s)
			}
		}
		return form{R: text.String()}, true
	}
	var L, R strings.Builder
	seen := false
	for _, b := range merged {
		if b.rep && b.b > 0 {
			seen = true
			continue
		}
		chunk := b.s
		if b.rep {
			chunk = strings.Repeat(b.s, b.a)
		}
		if seen {
			R.WriteString(chunk)
		} else {
			L.WriteString(chunk)
		}
	}
	ls, rs := L.String(), R.String()
	word, a, bcoef := rep.s, rep.a, rep.b
	for word != "" && strings.HasSuffix(ls, word) {
		ls = ls[:len(ls)-len(word)]
		a++
	}
	for word != "" && strings.HasPrefix(rs, word) {
		rs = rs[len(word):]
		a++
	}
	return form{L: ls, w: word, a: a, b: bcoef, R: rs}, true
}

func formsEqual(f1, f2 form) bool {
	if f1.b == 0 && f2.b == 0 {
		return f1.L+f1.R == f2.L+f2.R && f1.w == "" && f2.w == ""
	}
	if f1.b == 0 || f2.b == 0 {
		return false
	}
	if len(f1.w)*f1.b != len(f2.w)*f2.b {
		return false
	}
	for phase := 0; phase < len(f1.w); phase++ {
		if phase == 0 {
			if sameRep(f1.L, f1.w, f1.a, f1.b, f1.R, f2.L, f2.w, f2.a, f2.b, f2.R) {
				return true
			}
			continue
		}
		x, y := f1.w[:phase], f1.w[phase:]
		yw := y + x
		if yw == "" || f1.a-1 <= 0 {
			continue
		}
		if sameRep(f1.L+x, yw, f1.a-1, f1.b, y+f1.R, f2.L, f2.w, f2.a, f2.b, f2.R) {
			return true
		}
	}
	return false
}

func sameRep(L1, w1 string, a1, b1 int, R1, L2, w2 string, a2, b2 int, R2 string) bool {
	if w2 == "" {
		return false
	}
	for phase2 := 0; phase2 < len(w2); phase2++ {
		L, w, a, b, R := L2, w2, a2, b2, R2
		if phase2 != 0 {
			if a2-1 < 1 {
				continue
			}
			x, y := w2[:phase2], w2[phase2:]
			L, w, a, b, R = L2+x, y+x, a2-1, b2, y+R2
		}
		for w != "" && strings.HasSuffix(L, w) {
			L = L[:len(L)-len(w)]
			a++
		}
		for w != "" && strings.HasPrefix(R, w) {
			R = R[len(w):]
			a++
		}
		pw, pa, pb := primitive(w, a, b)
		for pw != "" && strings.HasSuffix(L, pw) {
			L = L[:len(L)-len(pw)]
			pa++
		}
		for pw != "" && strings.HasPrefix(R, pw) {
			R = R[len(pw):]
			pa++
		}
		qw, qa, qb := primitive(w1, a1, b1)
		LL, RR := L1, R1
		for qw != "" && strings.HasSuffix(LL, qw) {
			LL = LL[:len(LL)-len(qw)]
			qa++
		}
		for qw != "" && strings.HasPrefix(RR, qw) {
			RR = RR[len(qw):]
			qa++
		}
		if LL == L && RR == R && qw == pw && qa == pa && qb == pb {
			return true
		}
	}
	return false
}

func betterCanon(segs []aseg) ([]block, bool) {
	blocks := make([]block, 0, len(segs))
	for _, s := range segs {
		if s.wall {
			if s.s != "" {
				blocks = append(blocks, block{s.s, 1, 0})
			}
			continue
		}
		if s.a < 1 || s.b < 0 || s.w == "" {
			return nil, false
		}
		w, a, b := primitive(s.w, s.a, s.b)
		blocks = append(blocks, block{w, a, b})
	}
	rounds := len(blocks)*4 + 4
	for range rounds {
		filtered := make([]block, 0, len(blocks))
		for _, blk := range blocks {
			if blk.w != "" && !(blk.a == 0 && blk.b == 0) {
				filtered = append(filtered, blk)
			}
		}
		blocks = filtered
		merged := make([]block, 0, len(blocks))
		changed := false
		for _, blk := range blocks {
			if n := len(merged); n > 0 && merged[n-1].w == blk.w {
				merged[n-1].a += blk.a
				merged[n-1].b += blk.b
				changed = true
				continue
			}
			if n := len(merged); n > 0 && merged[n-1].a == 1 && merged[n-1].b == 0 && blk.a == 1 && blk.b == 0 {
				pw, pa, pb := primitive(merged[n-1].w+blk.w, 1, 0)
				merged[n-1] = block{pw, pa, pb}
				changed = true
				continue
			}
			merged = append(merged, blk)
		}
		blocks = merged
		absorbedAny := false
		neu := make([]block, 0, len(blocks))
		for i := 0; i < len(blocks); i++ {
			w, a, b := blocks[i].w, blocks[i].a, blocks[i].b
			raw := b == 0 && a == 1
			if len(neu) > 0 {
				pw, pa, pb := neu[len(neu)-1].w, neu[len(neu)-1].a, neu[len(neu)-1].b
				plastRaw := pb == 0 && pa == 1
				if !plastRaw && raw && pw != "" && strings.HasPrefix(w, pw) {
					rest := w
					cnt := 0
					for strings.HasPrefix(rest, pw) {
						rest = rest[len(pw):]
						cnt++
					}
					neu[len(neu)-1].a += cnt
					absorbedAny = true
					if rest != "" {
						neu = append(neu, block{rest, 1, 0})
					}
					continue
				}
				if plastRaw && !raw && w != "" && strings.HasSuffix(pw, w) {
					rest := pw
					cnt := 0
					for strings.HasSuffix(rest, w) {
						rest = rest[:len(rest)-len(w)]
						cnt++
					}
					a += cnt
					absorbedAny = true
					if rest != "" {
						neu[len(neu)-1] = block{rest, 1, 0}
						neu = append(neu, block{w, a, b})
					} else {
						neu[len(neu)-1] = block{w, a, b}
					}
					continue
				}
			}
			neu = append(neu, block{w, a, b})
		}
		blocks = neu
		if !changed && !absorbedAny {
			break
		}
	}
	for i, blk := range blocks {
		w, a, b := primitive(blk.w, blk.a, blk.b)
		blocks[i] = block{w, a, b}
	}
	out := make([]block, 0, len(blocks))
	for _, blk := range blocks {
		if n := len(out); n > 0 && out[n-1].w == blk.w {
			out[n-1].a += blk.a
			out[n-1].b += blk.b
			continue
		}
		if n := len(out); n > 0 && out[n-1].a == 1 && out[n-1].b == 0 && blk.a == 1 && blk.b == 0 {
			pw, pa, pb := primitive(out[n-1].w+blk.w, 1, 0)
			out[n-1] = block{pw, pa, pb}
			continue
		}
		out = append(out, blk)
	}
	filtered := make([]block, 0, len(out))
	for _, blk := range out {
		if blk.w != "" && !(blk.a == 0 && blk.b == 0) {
			filtered = append(filtered, blk)
		}
	}
	return filtered, true
}
