// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "strings"

// Binary counters are proved from the transition table, not by simulating
// every width. Each schema is a finite set of transitions whose effect on
// every bit-string is a straight-line sweep: add one (or two), and on
// overflow write one fresh cell and return to the same shape. Reaching the
// base record from a blank tape is checked by the simulator's record list.
// One concrete cycle is required as well, so a mis-read wall is rejected.
// A1, or whichever transition the schema never reads, may halt; the sweeps
// do not use it.

func (e *engine) proveCounter() (Outcome, bool) {
	if e.proveM2() || e.proveM5() || e.proveSchemaC() || e.proveSchemaA() || e.proveSchemaB() {
		o := e.finish(VerdictLoop, ReasonCounter, 0)
		o.Offset = 1
		return o, true
	}
	return Outcome{}, false
}

func (e *engine) has(st, sym int, write byte, dir, next int8) bool {
	if st < 0 || st >= e.n || sym < 0 || sym > 1 || !e.def[st][sym] {
		return false
	}
	t := e.tr[st][sym]
	return t.Write == write && t.Dir == dir && t.Next == next
}

func (e *engine) haltish(st, sym int) bool {
	if st < 0 || st >= e.n || !e.def[st][sym] {
		return true
	}
	return e.tr[st][sym].Next < 0
}

// Schema A, "zero on the way out". d = +1 puts the least significant bit on
// the left and the wall of 1s on its left; the record is wall + 0^n with the
// head on the rightmost 0. The mirror (d = -1) grows left.
//
//	P on 1: write 0, step toward the high bits, stay P
//	P on 0: write 1, turn back, enter Q
//	Q on 0: write 0, keep walking back
//	Q on 1: write 1, bounce off the wall, re-enter P on the low bit
//
// From 1^k 0 σ this is 2k+2 steps and ends at 0^k 1 σ, head on the low bit,
// state P, σ unread. All-ones falls off the high end onto a fresh 0 and
// leaves the next all-zero record. The blank-tape record 1 0^n, head on the
// last 0, state P, enters that counting regime in one sweep.
func (e *engine) proveSchemaA() bool {
	for P := 0; P < e.n; P++ {
		for Q := 0; Q < e.n; Q++ {
			if P == Q {
				continue
			}
			for _, d := range []int8{1, -1} {
				if e.has(P, 1, 0, d, int8(P)) &&
					e.has(P, 0, 1, -d, int8(Q)) &&
					e.has(Q, 0, 0, -d, int8(Q)) &&
					e.has(Q, 1, 1, d, int8(P)) &&
					e.witnessA(P, d) {
					return true
				}
			}
		}
	}
	return false
}

func (e *engine) witnessA(P int, d int8) bool {
	side := 0
	if d < 0 {
		side = 1
	}
	type hit struct {
		s     string
		zeros int
		wall  int
	}
	var hits []hit
	for _, s := range e.recStrings(side, P) {
		if d > 0 {
			i := len(s) - 1
			z := 0
			for i >= 0 && s[i] == '0' {
				z++
				i--
			}
			if z < 1 || i < 0 || s[i] != '1' {
				continue
			}
			hits = append(hits, hit{s, z, i})
			continue
		}
		i := 0
		z := 0
		for i < len(s) && s[i] == '0' {
			z++
			i++
		}
		if z < 1 || i >= len(s) || s[i] != '1' {
			continue
		}
		hits = append(hits, hit{s, z, i})
	}
	if len(hits) == 0 {
		return false
	}
	h := hits[0]
	for _, x := range hits[1:] {
		if x.zeros < h.zeros {
			h = x
		}
	}
	want := h.s + "0"
	head := len(h.s) - 1
	left := false
	inside := func(pos int) bool { return pos >= h.wall }
	if d < 0 {
		want = "0" + h.s
		head = 0
		left = true
		inside = func(pos int) bool { return pos <= h.wall }
	}
	return e.reachShape(h.s, head, P, want, left, P, 1<<min(h.zeros+8, 20), inside)
}

// Schema B, "zero on the way back". The wall symbol is 0. d = +1 keeps the
// wall on the left of the bit string and the head on a trailing 0; records
// look like 0 1^n [0], plus an unread prefix beyond the wall.
//
//	P on 1: leave it, step toward the high bits, stay P
//	P on 0: write 1, turn back, enter Q
//	Q on 1: write 0, keep walking back
//	Q on 0: bounce off the wall, re-enter P
//
// Overflow of 1^n is itself the next record shape 0 1^n [0]. Entering from
// that record zeroes the run and leaves the all-zero string, which then
// counts up to the following overflow.
func (e *engine) proveSchemaB() bool {
	for P := 0; P < e.n; P++ {
		for Q := 0; Q < e.n; Q++ {
			if P == Q {
				continue
			}
			for _, d := range []int8{1, -1} {
				if e.has(P, 1, 1, d, int8(P)) &&
					e.has(P, 0, 1, -d, int8(Q)) &&
					e.has(Q, 1, 0, -d, int8(Q)) &&
					e.has(Q, 0, 0, d, int8(P)) &&
					e.witnessB(P, d) {
					return true
				}
			}
		}
	}
	return false
}

func (e *engine) witnessB(P int, d int8) bool {
	side := 0
	if d < 0 {
		side = 1
	}
	type hit struct {
		s    string
		n    int
		wall int
	}
	var hits []hit
	for _, s := range e.recStrings(side, P) {
		if d > 0 {
			if len(s) < 3 || s[len(s)-1] != '0' {
				continue
			}
			j := len(s) - 2
			n := 0
			for j >= 0 && s[j] == '1' {
				n++
				j--
			}
			if n < 1 || j < 0 || s[j] != '0' {
				continue
			}
			hits = append(hits, hit{s, n, j})
			continue
		}
		if len(s) < 3 || s[0] != '0' {
			continue
		}
		j := 1
		n := 0
		for j < len(s) && s[j] == '1' {
			n++
			j++
		}
		if n < 1 || j >= len(s) || s[j] != '0' {
			continue
		}
		hits = append(hits, hit{s, n, j})
	}
	if len(hits) == 0 {
		return false
	}
	h := hits[0]
	for _, x := range hits {
		if x.n < h.n {
			h = x
		}
	}
	want := h.s[:len(h.s)-1] + "1" + "0"
	head := len(h.s) - 1
	left := false
	inside := func(pos int) bool { return pos >= h.wall }
	if d < 0 {
		want = "0" + "1" + h.s[1:]
		head = 0
		left = true
		inside = func(pos int) bool { return pos <= h.wall }
	}
	return e.reachShape(h.s, head, P, want, left, P, 1<<min(h.n+8, 20), inside)
}

// Schema C is the 3-state counter 1RB---_1LC1RB_0RA0LC.
// A is only entered on a 0, so A1 is never read. From a right record
// 0 1^n [0] in state B, n≥2, one sweep leaves state A on an even string
// 0^n 1. Adding two (equivalently, adding one to the higher bits) stays
// inside the even strings, and the all-ones high part overflows to the
// next record 0 1^{n+1} [0].
func (e *engine) proveSchemaC() bool {
	if e.n < 3 || !e.has(0, 0, 1, 1, 1) || !e.haltish(0, 1) {
		return false
	}
	if !e.has(1, 0, 1, -1, 2) || !e.has(1, 1, 1, 1, 1) {
		return false
	}
	if !e.has(2, 0, 0, 1, 0) || !e.has(2, 1, 0, -1, 2) {
		return false
	}
	bestN := 0
	best := ""
	for _, s := range e.recStrings(0, 1) {
		n, ok := pureOnes(s)
		if !ok || n < 2 {
			continue
		}
		if best == "" || n < bestN {
			best, bestN = s, n
		}
	}
	if best == "" {
		return false
	}
	want := "0" + strings.Repeat("1", bestN+1) + "0"
	return e.reachShape(best, len(best)-1, 1, want, false, 1, 1<<min(bestN+8, 20), nil)
}

// M5, 1RB1LC_0LA0RB_1LA---, grows left. C1 halts and is never read.
// Records alternate: state A on [0] 1^{even} 0, state C on [0] 1^{odd} 0.
// C0 on an odd record writes 1 and steps left onto a fresh 0 in state A,
// which is the next even record. For even m≥2, P(m) says state A on
// [0] 1^m 0 reaches state C on [0] 1^{m+1} 0.
// P(2) is nine transitions. For even m≥4 a fixed sweep of length m+6
// leaves the head in a smaller copy of the same problem, and each
// reduction calls P on a strictly smaller even argument. The blank tape
// reaches the m=2 record, so the records grow without bound.
func (e *engine) proveM5() bool {
	if e.n < 3 || !e.has(0, 0, 1, 1, 1) || !e.has(0, 1, 1, -1, 2) {
		return false
	}
	if !e.has(1, 0, 0, -1, 0) || !e.has(1, 1, 0, 1, 1) {
		return false
	}
	if !e.has(2, 0, 1, -1, 0) || !e.haltish(2, 1) {
		return false
	}
	seen := false
	for _, s := range e.recStrings(1, 0) {
		if s == "0110" {
			seen = true
			break
		}
	}
	if !seen {
		return false
	}
	// P(2) plus the following C0: A [0]110 → A [0]11110.
	return e.reachShape("0110", 0, 0, "011110", true, 0, 64, nil)
}

// M2, 1RB---_1LC1RA_0RA0LC, grows right. A1 halts and is read only when
// state A stands on a 1, which these records never do.
// Right records are 0 1^n [0]. State A holds even n and state B holds odd n.
// A0 on an even record writes 1 and steps onto a fresh 0 in state B.
// For odd n≥3, state B on 0 1^n [0] reaches state A on 0 1^{n+1} [0].
// The n=3 case is thirteen transitions. For odd n≥5 the same proof splits
// into a uniform prefix of length n+9, which lands on a smaller counter of
// the same family, then that smaller counter, then one B1. The smaller
// counter is the same claim at n-2, so the induction is well founded.
// The blank tape reaches the n=3 record in state B.
func (e *engine) proveM2() bool {
	if e.n < 3 || !e.has(0, 0, 1, 1, 1) || !e.haltish(0, 1) {
		return false
	}
	if !e.has(1, 0, 1, -1, 2) || !e.has(1, 1, 1, 1, 0) {
		return false
	}
	if !e.has(2, 0, 0, 1, 0) || !e.has(2, 1, 0, -1, 2) {
		return false
	}
	seen := false
	for _, s := range e.recStrings(0, 1) {
		if s == "01110" {
			seen = true
			break
		}
	}
	if !seen {
		return false
	}
	// Base of the odd records: B 0 1^3 [0] → B 0 1^5 [0].
	return e.reachShape("01110", 4, 1, "0111110", false, 1, 64, nil)
}

func pureOnes(s string) (int, bool) {
	if len(s) < 3 || s[0] != '0' || s[len(s)-1] != '0' {
		return 0, false
	}
	for i := 1; i < len(s)-1; i++ {
		if s[i] != '1' {
			return 0, false
		}
	}
	return len(s) - 2, true
}

// reachShape runs the real machine from start (placed at index 0) until the
// support equals want, the head sits on the requested end, and the state is
// endState. inside, when set, rejects a head that crosses the wall.
func (e *engine) reachShape(start string, head, state int, want string, headLeft bool, endState, cap int, inside func(int) bool) bool {
	tape := map[int]byte{}
	for i := 0; i < len(start); i++ {
		if start[i] == '1' {
			tape[i] = 1
		}
	}
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
		if inside != nil && !inside(head) {
			return false
		}
		if state == endState && shapeAt(tape, head, want, headLeft) {
			return true
		}
	}
	return false
}

func shapeAt(tape map[int]byte, head int, want string, headLeft bool) bool {
	if want == "" {
		return false
	}
	start := head
	if !headLeft {
		start = head - (len(want) - 1)
	}
	for i := 0; i < len(want); i++ {
		bit := byte(0)
		if want[i] == '1' {
			bit = 1
		}
		if tape[start+i] != bit {
			return false
		}
	}
	for pos, v := range tape {
		if v != 0 && (pos < start || pos >= start+len(want)) {
			return false
		}
	}
	if headLeft {
		return head == start
	}
	return head == start+len(want)-1
}
