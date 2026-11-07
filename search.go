// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

// SearchResult is the busy-beaver scoreboard for n-state 2-symbol machines.
// When Unknown is 0, S, Σ, and space are proved for this n, not just bounded.
// Otherwise the three machines are lower bounds: every reported halter really
// halts, and no proved non-halter was counted, but some machines were left open.
type SearchResult struct {
	N       int
	Limit   uint64
	Proved  bool
	Nodes   int
	Halted  int
	Looping int
	Unknown int

	Steps MachineScore
	Ones  MachineScore
	Space MachineScore

	// Open is a sample of machines the decider could not settle.
	Open []string
}

// MachineScore is one extreme halting machine.
type MachineScore struct {
	Spec  string
	Steps uint64
	Ones  int
	Space int
}

// Search enumerates n-state 2-symbol machines in tree normal form and decides
// each blank-tape run. Halt is a simulation witness. Loop is a cycler,
// a translated cycler, a closed non-halting graph, a bouncer, or a counter.
//
// For n ≥ 2 the first transition is fixed as 1RB. That does not drop the
// champion: a first write of 0 leaves a blank tape, a first step that stays
// in A on a blank tape never halts, and a first step left is the mirror of a
// first step right. New states are introduced in order, so state relabelings
// are not enumerated twice.
func Search(n int, limit uint64) SearchResult {
	if n < 1 || n > maxStates {
		return SearchResult{N: n, Limit: limit}
	}
	s := &searcher{
		n:     n,
		e:     newEngine(),
		limit: limit,
		cand:  make([][]Trans, n+1),
	}
	s.e.n = n
	s.e.limit = limit
	s.e.detect = true
	for u := 1; u <= n; u++ {
		s.cand[u] = transitionChoices(u, n)
	}
	if n == 1 {
		s.dfs(1)
	} else {
		s.e.tr[0][0] = Trans{Write: 1, Dir: 1, Next: 1, Def: true}
		s.e.def[0][0] = true
		s.dfs(2)
	}
	return s.result()
}

type searcher struct {
	n     int
	e     *engine
	limit uint64
	cand  [][]Trans

	nodes, halted, looping, unknown int
	steps                           MachineScore
	ones                            MachineScore
	space                           MachineScore
	have                            bool
	open                            []string
}

func (s *searcher) result() SearchResult {
	return SearchResult{
		N:       s.n,
		Limit:   s.limit,
		Proved:  s.unknown == 0,
		Nodes:   s.nodes,
		Halted:  s.halted,
		Looping: s.looping,
		Unknown: s.unknown,
		Steps:   s.steps,
		Ones:    s.ones,
		Space:   s.space,
		Open:    s.open,
	}
}

func (s *searcher) dfs(used int) {
	s.e.n = s.n
	s.e.limit = s.limit
	s.e.detect = true
	s.e.reset()
	s.nodes++
	o := s.e.exec()
	switch o.Verdict {
	case VerdictHalt:
		s.halted++
		s.note(o)
	case VerdictLoop:
		s.looping++
	case VerdictUnknown:
		s.unknown++
		if len(s.open) < 8 {
			s.open = append(s.open, s.spec())
		}
	case verdictNeed:
		st, sy := o.NeedState, o.NeedSym
		for _, t := range s.cand[used] {
			s.e.tr[st][sy] = t
			s.e.def[st][sy] = true
			nu := used
			if int(t.Next) == used {
				nu = used + 1
			}
			s.dfs(nu)
			s.e.def[st][sy] = false
		}
	}
}

func (s *searcher) note(o Outcome) {
	spec := s.spec()
	sc := MachineScore{Spec: spec, Steps: o.Steps, Ones: o.Ones, Space: o.Space}
	if !s.have || sc.Steps > s.steps.Steps || (sc.Steps == s.steps.Steps && sc.Ones > s.steps.Ones) {
		s.steps = sc
	}
	if !s.have || sc.Ones > s.ones.Ones || (sc.Ones == s.ones.Ones && sc.Steps > s.ones.Steps) {
		s.ones = sc
	}
	if !s.have || sc.Space > s.space.Space || (sc.Space == s.space.Space && sc.Steps > s.space.Steps) {
		s.space = sc
	}
	s.have = true
}

func (s *searcher) spec() string {
	t := make([][2]Trans, s.n)
	for i := 0; i < s.n; i++ {
		for sym := 0; sym < 2; sym++ {
			if s.e.def[i][sym] {
				t[i][sym] = s.e.tr[i][sym]
				t[i][sym].Def = true
			}
		}
	}
	return Format(s.n, t)
}

// transitionChoices lists TNF-legal ways to fill one undefined transition
// when `used` states have already been introduced.
// The halting transition's direction does not affect steps, ones, or space
// (the cell it moves onto is never read), so only a right move is emitted.
func transitionChoices(used, n int) []Trans {
	var ts []Trans
	for _, w := range []byte{1, 0} {
		for _, d := range []int8{1, -1} {
			for st := 0; st < used; st++ {
				ts = append(ts, Trans{Write: w, Dir: d, Next: int8(st), Def: true})
			}
			if used < n {
				ts = append(ts, Trans{Write: w, Dir: d, Next: int8(used), Def: true})
			}
		}
	}
	ts = append(ts,
		Trans{Write: 1, Dir: 1, Next: -1, Def: true},
		Trans{Write: 0, Dir: 1, Next: -1, Def: true},
	)
	return ts
}

// Exhaustive decides every n-state machine, with no symmetry reduction.
// It is the check on Search for n small enough that (4(n+1))^(2n) is tiny.
func Exhaustive(n int, limit uint64) SearchResult {
	opts := allTransitions(n)
	s := &searcher{n: n, e: newEngine(), limit: limit}
	s.e.n = n
	s.e.limit = limit
	s.e.detect = true
	var fill func(i int)
	fill = func(i int) {
		if i == 2*n {
			s.e.n = n
			s.e.limit = limit
			s.e.detect = true
			s.e.reset()
			s.nodes++
			o := s.e.exec()
			switch o.Verdict {
			case VerdictHalt:
				s.halted++
				s.note(o)
			case VerdictLoop:
				s.looping++
			default:
				s.unknown++
			}
			return
		}
		st, sy := i/2, i%2
		for _, t := range opts {
			s.e.tr[st][sy] = t
			s.e.def[st][sy] = true
			fill(i + 1)
		}
	}
	fill(0)
	return s.result()
}

func allTransitions(n int) []Trans {
	var ts []Trans
	for _, w := range []byte{0, 1} {
		for _, d := range []int8{-1, 1} {
			for st := 0; st < n; st++ {
				ts = append(ts, Trans{Write: w, Dir: d, Next: int8(st), Def: true})
			}
			ts = append(ts, Trans{Write: w, Dir: d, Next: -1, Def: true})
		}
	}
	return ts
}
