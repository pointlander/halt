// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"strings"
	"unicode"
)

// A Turing machine in the busy-beaver model: n states, symbols {0, 1},
// a single two-way infinite tape, and an explicit halting transition.
// The machine starts in state A on a blank (all-zero) tape.
//
// A transition is written in the standard text format used by the Busy
// Beaver Challenge: a write symbol, a direction, and a next state.
// "1RB" writes 1, moves right, and enters state B. "1RH" and "1RZ" are
// halting transitions. "---" is an undefined transition; reaching one
// halts without writing or moving.
type Trans struct {
	Write byte // 0 or 1
	Dir   int8 // -1 left, +1 right
	Next  int8 // -1 halts, otherwise a state index
	Def   bool
}

// Machine is a complete or partial transition table.
// T[state][symbol] is the transition read when that state sees that symbol.
type Machine struct {
	N int
	T [][2]Trans
}

// Champions are the known busiest beavers on a blank tape.
// S is the number of steps (shifts), including the halting transition.
// Σ is the number of 1s left on the tape.
// The 3-state row is a Σ champion (14 steps, six 1s). S(3) is 21 and is
// found by search; that machine leaves only five 1s.
var Champions = []struct {
	N     int
	Spec  string
	Steps uint64
	Ones  int
}{
	{1, "1RH", 1, 1},
	{2, "1RB1LB_1LA1RH", 6, 4},
	{3, "1RB1RH_0RC1RB_1LC1LA", 14, 6},
	{4, "1RB1LB_1LA0LC_1RH1LD_1RD0RA", 107, 13},
	{5, "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 47_176_870, 4098},
}

// Parse reads a machine in standard text format.
//
//	1RB1LB_1LA1RH
//	1RB 1LB 1LA 1RH
//	1RH
//
// State letters are A, B, C, … in order. H and Z both mean halt.
func Parse(spec string) (Machine, error) {
	fields := splitSpec(spec)
	if len(fields) == 0 {
		return Machine{}, fmt.Errorf("empty machine")
	}
	var trans []Trans
	for _, f := range fields {
		if len(f) == 6 && !strings.Contains(f, "-") {
			a, err := parseOne(f[:3])
			if err != nil {
				return Machine{}, err
			}
			b, err := parseOne(f[3:])
			if err != nil {
				return Machine{}, err
			}
			trans = append(trans, a, b)
			continue
		}
		if len(f)%3 != 0 {
			return Machine{}, fmt.Errorf("bad transition %q", f)
		}
		for i := 0; i < len(f); i += 3 {
			t, err := parseOne(f[i : i+3])
			if err != nil {
				return Machine{}, err
			}
			trans = append(trans, t)
		}
	}
	if len(trans)%2 != 0 {
		// A lone transition is A0, with A1 left undefined.
		trans = append(trans, Trans{})
	}
	n := len(trans) / 2
	for _, t := range trans {
		if t.Def && t.Next >= int8(n) {
			n = int(t.Next) + 1
		}
	}
	if n > maxStates {
		return Machine{}, fmt.Errorf("too many states (%d)", n)
	}
	m := Machine{N: n, T: make([][2]Trans, n)}
	for i, t := range trans {
		if i/2 >= n {
			break
		}
		m.T[i/2][i%2] = t
	}
	return m, nil
}

func splitSpec(spec string) []string {
	spec = strings.TrimSpace(spec)
	if spec == "" {
		return nil
	}
	var b strings.Builder
	for _, r := range spec {
		if unicode.IsSpace(r) || r == '_' || r == ';' || r == ',' {
			b.WriteByte(' ')
			continue
		}
		b.WriteRune(unicode.ToUpper(r))
	}
	return strings.Fields(b.String())
}

func parseOne(s string) (Trans, error) {
	if s == "---" {
		return Trans{}, nil
	}
	if len(s) != 3 {
		return Trans{}, fmt.Errorf("bad transition %q", s)
	}
	if s[0] != '0' && s[0] != '1' {
		return Trans{}, fmt.Errorf("bad write symbol in %q", s)
	}
	var dir int8
	switch s[1] {
	case 'L':
		dir = -1
	case 'R':
		dir = 1
	default:
		return Trans{}, fmt.Errorf("bad direction in %q", s)
	}
	var next int8
	switch s[2] {
	case 'H', 'Z':
		next = -1
	default:
		if s[2] < 'A' || s[2] > 'Y' {
			return Trans{}, fmt.Errorf("bad state in %q", s)
		}
		next = int8(s[2] - 'A')
	}
	return Trans{Write: s[0] - '0', Dir: dir, Next: next, Def: true}, nil
}

// Format renders a machine in standard text format.
// Undefined transitions are "---". Halt is written as H.
func Format(n int, t [][2]Trans) string {
	var b strings.Builder
	for s := 0; s < n; s++ {
		if s > 0 {
			b.WriteByte('_')
		}
		for sym := 0; sym < 2; sym++ {
			tr := t[s][sym]
			if !tr.Def {
				b.WriteString("---")
				continue
			}
			b.WriteByte('0' + tr.Write)
			if tr.Dir < 0 {
				b.WriteByte('L')
			} else {
				b.WriteByte('R')
			}
			if tr.Next < 0 {
				b.WriteByte('H')
			} else {
				b.WriteByte('A' + byte(tr.Next))
			}
		}
	}
	return b.String()
}

func (m Machine) String() string {
	return Format(m.N, m.T)
}
