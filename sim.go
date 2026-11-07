// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"math"
	"strings"
)

const maxStates = 16

// Verdict is what a partial decider may honestly report.
// Halt and Loop are proofs. Unknown means the bounds ran out.
type Verdict int

const (
	VerdictHalt Verdict = iota
	VerdictLoop
	VerdictUnknown
	// verdictNeed is internal: the simulator hit an undefined transition
	// and the caller (search) must choose one.
	verdictNeed
)

// Reason names the witness behind a verdict.
type Reason int

const (
	ReasonHalt Reason = iota
	ReasonUndefined
	ReasonCycler
	ReasonTranslated
	ReasonNoHalt
	ReasonBounce
	ReasonCounter
	ReasonK
	ReasonLimit
	ReasonNeed
)

func (r Reason) String() string {
	switch r {
	case ReasonHalt:
		return "halted"
	case ReasonUndefined:
		return "undefined transition"
	case ReasonCycler:
		return "cycler"
	case ReasonTranslated:
		return "translated cycler"
	case ReasonNoHalt:
		return "no halting transition"
	case ReasonBounce:
		return "bouncer"
	case ReasonCounter:
		return "binary counter"
	case ReasonK:
		return "program-size complexity"
	case ReasonLimit:
		return "step limit"
	default:
		return "undefined transition"
	}
}

// Outcome is a witnessed run from a blank tape.
type Outcome struct {
	Verdict Verdict
	Reason  Reason
	Steps   uint64
	Ones    int
	Space   int
	// Loop witness. Period is the cycle length in steps.
	// Offset is the head shift over one period (0 for an exact cycler).
	// Start is the step at which the repeated configuration first appeared.
	Period uint64
	Offset int
	Start  uint64
	Side   string
	// Need state/symbol when Verdict is verdictNeed.
	NeedState int
	NeedSym   int
	Tape      string
	// KBits is the length of this machine's prefix-free program.
	// KBound is the proved step cutoff Σ_H for programs of that length.
	// KExact means K(Steps) equals KBits, not only an upper bound.
	KBits  int
	KBound uint64
	KExact bool
}

func (o Outcome) Status() string {
	switch o.Verdict {
	case VerdictHalt:
		return "halts"
	case VerdictLoop:
		return "loops"
	default:
		return "unknown"
	}
}

// ekey is an exact tape configuration packed into machine words.
// Cells outside [min, min+n) are 0. n is at most 256.
type ekey struct {
	state uint8
	n     uint16
	head  int32
	min   int32
	b     [4]uint64
}

func (k ekey) hash() uint64 {
	h := uint64(k.state) ^ uint64(k.n)<<8
	h = h*0x9E3779B185EBCA87 + uint64(uint32(k.head))
	h = h*0x9E3779B185EBCA87 + uint64(uint32(k.min))
	for _, w := range k.b {
		h = h*0x9E3779B185EBCA87 + w
	}
	h ^= h >> 33
	h *= 0xff51afd7ed558ccd
	h ^= h >> 33
	return h
}

func (k ekey) eq(o ekey) bool {
	return k.state == o.state && k.n == o.n && k.head == o.head && k.min == o.min && k.b == o.b
}

// set is an open-addressed configuration set.
// reset bumps a generation counter, so clearing between machines is O(1).
type set struct {
	slots []slot
	gen   uint32
	live  int
}

type slot struct {
	gen  uint32
	time uint32
	key  ekey
}

func (s *set) reset() {
	s.gen++
	if s.gen == 0 {
		for i := range s.slots {
			s.slots[i].gen = 0
		}
		s.gen = 1
	}
	s.live = 0
	if len(s.slots) == 0 {
		s.slots = make([]slot, 1024)
	}
}

// seen reports whether k is already present. If not, it inserts k at time t
// unless the set is over cap, in which case stored is false.
func (s *set) seen(k ekey, t uint32, cap int) (already bool, first uint32, stored bool) {
	if s.live*10 >= len(s.slots)*7 {
		s.grow()
	}
	if cap > 0 && s.live >= cap {
		// Still probe so a repeat of a stored configuration is noticed.
		if ok, ft := s.lookup(k); ok {
			return true, ft, true
		}
		return false, 0, false
	}
	mask := uint64(len(s.slots) - 1)
	i := k.hash() & mask
	for {
		sl := &s.slots[i]
		if sl.gen != s.gen {
			sl.gen = s.gen
			sl.time = t
			sl.key = k
			s.live++
			return false, t, true
		}
		if sl.key.eq(k) {
			return true, sl.time, true
		}
		i = (i + 1) & mask
	}
}

func (s *set) lookup(k ekey) (bool, uint32) {
	mask := uint64(len(s.slots) - 1)
	i := k.hash() & mask
	for {
		sl := &s.slots[i]
		if sl.gen != s.gen {
			return false, 0
		}
		if sl.key.eq(k) {
			return true, sl.time
		}
		i = (i + 1) & mask
	}
}

func (s *set) grow() {
	old := s.slots
	s.slots = make([]slot, len(old)*2)
	gen := s.gen
	live := 0
	mask := uint64(len(s.slots) - 1)
	for i := range old {
		if old[i].gen != gen {
			continue
		}
		j := old[i].key.hash() & mask
		for s.slots[j].gen == gen {
			j = (j + 1) & mask
		}
		s.slots[j] = old[i]
		live++
	}
	s.live = live
}

// rec is a snapshot of the tape at a record-breaking configuration,
// before the transition at that step is applied.
type rec struct {
	state int8
	head  int32
	time  uint32
	min   int32
	n     uint16
	b     [4]uint64
}

// engine simulates one machine. Buffers are reused across runs.
type engine struct {
	n   int
	tr  [maxStates][2]Trans
	def [maxStates][2]bool

	c      []byte
	v      []int32
	base   int
	dirtyL int
	dirtyR int

	head   int
	minAbs int
	maxAbs int
	seenR  bool

	steps uint64
	limit uint64

	hist     set
	histCap  int
	recCap   int
	wantTape bool

	recs [2][maxStates][]rec
	rn   [2][maxStates]int
	extR int
	extL int

	detect bool
}

func newEngine() *engine {
	e := &engine{
		c:       make([]byte, 256),
		v:       make([]int32, 256),
		histCap: 2_000_000,
		recCap:  4_000,
	}
	for i := range e.v {
		e.v[i] = -1
	}
	e.base = -128
	e.dirtyL = len(e.c)
	e.dirtyR = 0
	return e
}

func (e *engine) load(m Machine) {
	e.n = m.N
	for s := 0; s < maxStates; s++ {
		e.def[s] = [2]bool{}
		e.tr[s] = [2]Trans{}
	}
	for s := 0; s < m.N; s++ {
		for sym := 0; sym < 2; sym++ {
			e.tr[s][sym] = m.T[s][sym]
			e.def[s][sym] = m.T[s][sym].Def
		}
	}
}

func (e *engine) reset() {
	if e.dirtyL < e.dirtyR {
		for i := e.dirtyL; i < e.dirtyR; i++ {
			e.c[i] = 0
			e.v[i] = -1
		}
	}
	e.dirtyL = len(e.c)
	e.dirtyR = 0
	e.head = 0
	e.minAbs = 0
	e.maxAbs = 0
	e.seenR = false
	e.steps = 0
	e.extR = 0
	e.extL = 0
	e.hist.reset()
	for side := 0; side < 2; side++ {
		for s := 0; s < maxStates; s++ {
			e.rn[side][s] = 0
		}
	}
}

func (e *engine) ensure(abs int) int {
	if len(e.c) == 0 {
		e.expand()
	}
	for abs < e.base || abs >= e.base+len(e.c) {
		e.expand()
	}
	return abs - e.base
}

func (e *engine) expand() {
	n := len(e.c)
	if n == 0 {
		n = 256
		e.c = make([]byte, n)
		e.v = make([]int32, n)
		for i := range e.v {
			e.v[i] = -1
		}
		e.base = -n / 2
		e.dirtyL = len(e.c)
		e.dirtyR = 0
		return
	}
	nc := make([]byte, n*2)
	nv := make([]int32, n*2)
	for i := range nv {
		nv[i] = -1
	}
	copy(nc[n/2:], e.c)
	copy(nv[n/2:], e.v)
	if e.dirtyL < e.dirtyR {
		e.dirtyL += n / 2
		e.dirtyR += n / 2
	} else {
		e.dirtyL = len(nc)
		e.dirtyR = 0
	}
	e.base -= n / 2
	e.c = nc
	e.v = nv
}

func (e *engine) touch(i int) {
	if i < e.dirtyL {
		e.dirtyL = i
	}
	if i+1 > e.dirtyR {
		e.dirtyR = i + 1
	}
}

func (e *engine) markSpan(abs int) {
	if !e.seenR {
		e.minAbs = abs
		e.maxAbs = abs
		e.seenR = true
		return
	}
	if abs < e.minAbs {
		e.minAbs = abs
	}
	if abs > e.maxAbs {
		e.maxAbs = abs
	}
}

// pack snapshots symbols on [minAbs, maxAbs] and the absolute head.
// ok is false when the span does not fit in 256 cells.
func (e *engine) packKey(state int) (ekey, bool) {
	n := e.maxAbs - e.minAbs + 1
	if !e.seenR || n <= 0 || n > 256 {
		return ekey{}, false
	}
	k := ekey{
		state: uint8(state),
		n:     uint16(n),
		head:  int32(e.head),
		min:   int32(e.minAbs),
	}
	for abs := e.minAbs; abs <= e.maxAbs; abs++ {
		i := abs - e.base
		if i < 0 || i >= len(e.c) || e.c[i] == 0 {
			continue
		}
		bit := abs - e.minAbs
		k.b[bit>>6] |= 1 << uint(bit&63)
	}
	return k, true
}

func (e *engine) symbol(abs int) byte {
	if abs < e.base || abs >= e.base+len(e.c) {
		return 0
	}
	return e.c[abs-e.base]
}

func bitAt(b [4]uint64, min int32, n uint16, abs int) byte {
	if abs < int(min) || abs >= int(min)+int(n) {
		return 0
	}
	bit := abs - int(min)
	if b[bit>>6]&(1<<uint(bit&63)) != 0 {
		return 1
	}
	return 0
}

func (e *engine) ones() int {
	c := 0
	if e.dirtyL < e.dirtyR {
		for _, b := range e.c[e.dirtyL:e.dirtyR] {
			c += int(b)
		}
	}
	return c
}

func (e *engine) space() int {
	if !e.seenR {
		return 0
	}
	return e.maxAbs - e.minAbs + 1
}

// picture draws the used tape with the head cell in brackets.
// One blank cell of context is kept on each side.
func (e *engine) picture() string {
	if !e.seenR && e.steps == 0 {
		return "[0]"
	}
	lo := e.minAbs
	hi := e.maxAbs
	if e.head < lo {
		lo = e.head
	}
	if e.head > hi {
		hi = e.head
	}
	lo--
	hi++
	var b strings.Builder
	for abs := lo; abs <= hi; abs++ {
		if abs != lo {
			b.WriteByte(' ')
		}
		sym := e.symbol(abs)
		if abs == e.head {
			b.WriteByte('[')
			b.WriteByte('0' + sym)
			b.WriteByte(']')
		} else {
			b.WriteByte('0' + sym)
		}
	}
	return b.String()
}

func (e *engine) finish(verdict Verdict, reason Reason, state int) Outcome {
	o := Outcome{
		Verdict: verdict,
		Reason:  reason,
		Steps:   e.steps,
		Ones:    e.ones(),
		Space:   e.space(),
	}
	if e.wantTape {
		o.Tape = e.picture()
	}
	if state >= 0 {
		o.NeedState = state
	}
	return o
}

func abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

// exec runs from a blank tape until halt, a proved loop, an undefined
// transition, or the step limit.
//
// Loop proofs are a repeated configuration (a cycler), a record-breaking
// configuration repeated one shift away (a translated cycler), a closed
// non-halting transition graph, a bouncer whose repeated block grows by a
// fixed word, or a binary counter read off the transition table.
// closedNonHalting reports whether every transition reachable from state A
// is defined and does not halt. Such a machine cannot halt: every step it
// will ever take is already a non-halting instruction. Unused states are
// ignored, so a partial table still qualifies when the live states are closed.
func (e *engine) closedNonHalting() bool {
	if e.n <= 0 {
		return false
	}
	seen := make([]bool, e.n)
	stack := []int{0}
	seen[0] = true
	for len(stack) > 0 {
		s := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		for sym := 0; sym < 2; sym++ {
			if !e.def[s][sym] || e.tr[s][sym].Next < 0 {
				return false
			}
			nxt := int(e.tr[s][sym].Next)
			if nxt < 0 || nxt >= e.n || seen[nxt] {
				continue
			}
			seen[nxt] = true
			stack = append(stack, nxt)
		}
	}
	return true
}

func (e *engine) exec() Outcome {
	if e.detect && e.closedNonHalting() {
		return e.finish(VerdictLoop, ReasonNoHalt, 0)
	}
	state := 0
	for e.steps < e.limit {
		i := e.ensure(e.head)
		e.touch(i)
		// Space counts cells that are read. The cell moved onto by a
		// halting transition is not read, so the bound is updated here.
		readPos := e.head
		e.markSpan(readPos)

		if e.detect {
			if e.steps > uint64(math.MaxUint32) {
				e.detect = false
			} else {
				if o, ok := e.observe(state); ok {
					return o
				}
			}
		}

		sym := e.c[i]
		if state < 0 || state >= e.n || !e.def[state][sym] {
			o := e.finish(verdictNeed, ReasonNeed, state)
			o.NeedState = state
			o.NeedSym = int(sym)
			// Reaching an undefined transition on a fully specified
			// machine is a halt with no write and no move. Search sets
			// detect and treats verdictNeed itself; Simulate/Decide of a
			// parsed machine uses haltOnUndef.
			return o
		}
		tr := e.tr[state][sym]
		e.c[i] = tr.Write
		e.head += int(tr.Dir)
		e.steps++
		if tr.Next < 0 {
			// Head sits on the cell the halting transition moved onto.
			e.ensure(e.head)
			return e.finish(VerdictHalt, ReasonHalt, -1)
		}
		state = int(tr.Next)
	}
	e.ensure(e.head)
	if e.detect {
		if o, ok := e.proveCounter(); ok {
			return o
		}
		if o, ok := e.proveBouncer(); ok {
			return o
		}
	}
	return e.finish(VerdictUnknown, ReasonLimit, state)
}

// observe applies the cycler and translated-cycler tests to the
// configuration about to be stepped. A true result is a loop proof.
func (e *engine) observe(state int) (Outcome, bool) {
	t := uint32(e.steps)
	i := e.head - e.base
	e.v[i] = int32(t)

	if k, ok := e.packKey(state); ok {
		already, first, _ := e.hist.seen(k, t, e.histCap)
		if already {
			o := e.finish(VerdictLoop, ReasonCycler, state)
			o.Period = e.steps - uint64(first)
			o.Start = uint64(first)
			o.Offset = 0
			return o, true
		}
	}

	side := -1
	if e.head > e.extR {
		e.extR = e.head
		side = 0
	} else if e.head < e.extL {
		e.extL = e.head
		side = 1
	}
	if side >= 0 {
		if o, ok := e.checkRecords(state, side, t); ok {
			return o, true
		}
		e.saveRecord(state, side, t)
	}
	return Outcome{}, false
}

func (e *engine) saveRecord(state, side int, t uint32) {
	if e.rn[side][state] >= e.recCap {
		return
	}
	k, ok := e.packKey(state)
	if !ok {
		return
	}
	r := rec{state: int8(state), head: int32(e.head), time: t, min: k.min, n: k.n, b: k.b}
	n := e.rn[side][state]
	if n == len(e.recs[side][state]) {
		e.recs[side][state] = append(e.recs[side][state], r)
	} else {
		e.recs[side][state][n] = r
	}
	e.rn[side][state] = n + 1
}

func (e *engine) checkRecords(state, side int, t uint32) (Outcome, bool) {
	n := e.rn[side][state]
	list := e.recs[side][state][:n]
	for i := range list {
		older := &list[i]
		L := e.distanceL(older, side, t)
		if !e.sameWindow(older, L, side) {
			continue
		}
		o := e.finish(VerdictLoop, ReasonTranslated, state)
		o.Period = e.steps - uint64(older.time)
		o.Start = uint64(older.time)
		o.Offset = e.head - int(older.head)
		if side == 0 {
			o.Side = "right"
		} else {
			o.Side = "left"
		}
		return o, true
	}
	return Outcome{}, false
}

// distanceL is the farthest the head traveled inward from the older
// record between then and now. Cells past the older record are ignored:
// they were blank at that record, as is the blank region past the new one.
func (e *engine) distanceL(older *rec, side int, currTime uint32) int {
	L := 0
	olderPos := int(older.head)
	lo := e.minAbs
	hi := e.maxAbs
	for abs := lo; abs <= hi; abs++ {
		if side == 0 && abs > olderPos {
			continue
		}
		if side == 1 && abs < olderPos {
			continue
		}
		i := abs - e.base
		if i < 0 || i >= len(e.v) {
			continue
		}
		vt := e.v[i]
		if vt < 0 {
			continue
		}
		if uint32(vt) >= older.time && uint32(vt) <= currTime {
			d := abs - olderPos
			if d < 0 {
				d = -d
			}
			if d > L {
				L = d
			}
		}
	}
	return L
}

func (e *engine) sameWindow(older *rec, L, side int) bool {
	step := -1
	if side == 1 {
		step = 1
	}
	for off := 0; abs(off) <= L; off += step {
		cur := e.symbol(e.head + off)
		old := bitAt(older.b, older.min, older.n, int(older.head)+off)
		if cur != old {
			return false
		}
	}
	return true
}

// Simulate runs m for at most limit steps and does not try to prove loops.
// A halt result is a witness. Hitting the limit yields Unknown.
func Simulate(m Machine, limit uint64) Outcome {
	e := newEngine()
	e.load(m)
	e.limit = limit
	e.detect = false
	e.wantTape = true
	e.reset()
	o := e.exec()
	if o.Verdict == verdictNeed {
		// Undefined transition: halt in place, no write.
		o.Verdict = VerdictHalt
		o.Reason = ReasonUndefined
	}
	return o
}

// Decide is a partial halting decider for a blank-tape run of m.
// Halt and Loop are proved. Unknown means limit (or the history cap)
// was not enough.
func Decide(m Machine, limit uint64) Outcome {
	e := newEngine()
	e.load(m)
	e.limit = limit
	e.detect = true
	e.wantTape = true
	e.reset()
	o := e.exec()
	if o.Verdict == verdictNeed {
		o.Verdict = VerdictHalt
		o.Reason = ReasonUndefined
	}
	return o
}

// Trace records every configuration up to halt, loop, or limit.
// The final outcome's tape is the tape after the last transition.
type Step struct {
	N     uint64
	State string
	Tape  string
}

func Trace(m Machine, limit uint64) (Outcome, []Step) {
	e := newEngine()
	e.load(m)
	e.limit = limit
	e.detect = true
	e.reset()
	var steps []Step
	state := 0
	for e.steps < e.limit {
		i := e.ensure(e.head)
		e.touch(i)
		e.markSpan(e.head)
		steps = append(steps, Step{
			N:     e.steps,
			State: stateName(state),
			Tape:  e.picture(),
		})
		if e.detect {
			if o, ok := e.observe(state); ok {
				return o, steps
			}
		}
		sym := e.c[i]
		if state < 0 || state >= e.n || !e.def[state][sym] {
			o := e.finish(VerdictHalt, ReasonUndefined, state)
			return o, steps
		}
		tr := e.tr[state][sym]
		e.c[i] = tr.Write
		e.head += int(tr.Dir)
		e.steps++
		if tr.Next < 0 {
			e.ensure(e.head)
			steps = append(steps, Step{N: e.steps, State: "H", Tape: e.picture()})
			return e.finish(VerdictHalt, ReasonHalt, -1), steps
		}
		state = int(tr.Next)
	}
	e.ensure(e.head)
	return e.finish(VerdictUnknown, ReasonLimit, state), steps
}

func stateName(s int) string {
	if s < 0 {
		return "H"
	}
	return string(rune('A' + s))
}
