// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "testing"

func TestChampions(t *testing.T) {
	for _, c := range Champions {
		m, err := Parse(c.Spec)
		if err != nil {
			t.Fatalf("BB(%d) %s: %v", c.N, c.Spec, err)
		}
		if m.N != c.N {
			t.Fatalf("BB(%d) parsed as %d states", c.N, m.N)
		}
		o := Simulate(m, c.Steps+10)
		if o.Verdict != VerdictHalt || o.Steps != c.Steps || o.Ones != c.Ones {
			t.Fatalf("BB(%d) %s: got %s steps=%d ones=%d space=%d tape=%s, want halt steps=%d ones=%d",
				c.N, c.Spec, o.Status(), o.Steps, o.Ones, o.Space, o.Tape, c.Steps, c.Ones)
		}
	}
}

func TestDecideLoopAndHalt(t *testing.T) {
	halt, err := Parse("1RH")
	if err != nil {
		t.Fatal(err)
	}
	o := Decide(halt, 100)
	if o.Verdict != VerdictHalt || o.Steps != 1 || o.Ones != 1 || o.Space != 1 {
		t.Fatalf("1RH: %+v", o)
	}

	// Writes 1s forever to the right: a translated cycler of period 1.
	sweep, err := Parse("1RA")
	if err != nil {
		t.Fatal(err)
	}
	o = Decide(sweep, 1000)
	if o.Verdict != VerdictLoop || o.Reason != ReasonTranslated {
		t.Fatalf("1RA: %+v", o)
	}
	if o.Offset != 1 || o.Period != 1 {
		t.Fatalf("1RA witness: offset=%d period=%d start=%d", o.Offset, o.Period, o.Start)
	}

	// Bounces between two blank cells. Exact cycle, period 2.
	bounce, err := Parse("0RB1RH_0LA1RH")
	if err != nil {
		t.Fatal(err)
	}
	o = Decide(bounce, 1000)
	if o.Verdict != VerdictLoop || o.Reason != ReasonCycler || o.Period != 2 {
		t.Fatalf("bounce: %+v", o)
	}

	// Published translated cycler (bbchallenge #44394115). Must not be called a halter.
	tc, err := Parse("1RB0RE_0LC1RC_0RD1LA_1LE---_1LB1RC")
	if err != nil {
		t.Fatal(err)
	}
	o = Decide(tc, 10_000)
	if o.Verdict != VerdictLoop || o.Reason != ReasonTranslated {
		t.Fatalf("translated cycler: %s %+v", o.Status(), o)
	}
}

func TestBB2Trace(t *testing.T) {
	m, err := Parse("1RB1LB_1LA1RH")
	if err != nil {
		t.Fatal(err)
	}
	o, steps := Trace(m, 100)
	if o.Verdict != VerdictHalt || o.Steps != 6 || o.Ones != 4 || o.Space != 4 {
		t.Fatalf("trace outcome: %+v", o)
	}
	if len(steps) != 7 { // 6 configurations plus the halted one
		t.Fatalf("trace length %d", len(steps))
	}
	last := steps[len(steps)-1]
	if last.State != "H" || last.Tape != "0 1 1 [1] 1 0" {
		t.Fatalf("final trace %s %s", last.State, last.Tape)
	}
}

func TestSearchMatchesExhaustive(t *testing.T) {
	for n := 1; n <= 2; n++ {
		lim := defaultLimit(n)
		s := Search(n, lim)
		e := Exhaustive(n, lim)
		if !s.Proved || !e.Proved {
			t.Fatalf("n=%d not fully decided: search unknown=%d exhaustive unknown=%d", n, s.Unknown, e.Unknown)
		}
		if s.Steps.Steps != e.Steps.Steps || s.Ones.Ones != e.Ones.Ones || s.Space.Space != e.Space.Space {
			t.Fatalf("n=%d search S=%d Σ=%d space=%d, exhaustive S=%d Σ=%d space=%d",
				n, s.Steps.Steps, s.Ones.Ones, s.Space.Space, e.Steps.Steps, e.Ones.Ones, e.Space.Space)
		}
	}
}

func TestSearchKnownValues(t *testing.T) {
	want := []struct {
		n     int
		steps uint64
		ones  int
		space int
	}{
		{1, 1, 1, 1},
		{2, 6, 4, 4},
		{3, 21, 6, 7},
	}
	for _, w := range want {
		r := Search(w.n, defaultLimit(w.n))
		if !r.Proved {
			t.Fatalf("n=%d unknown=%d open=%v", w.n, r.Unknown, r.Open)
		}
		if r.Steps.Steps != w.steps || r.Ones.Ones != w.ones || r.Space.Space != w.space {
			t.Fatalf("n=%d got S=%d (%s) Σ=%d (%s) space=%d (%s)",
				w.n, r.Steps.Steps, r.Steps.Spec, r.Ones.Ones, r.Ones.Spec, r.Space.Space, r.Space.Spec)
		}
	}
}

func TestParseFormat(t *testing.T) {
	in := "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA"
	m, err := Parse(in)
	if err != nil {
		t.Fatal(err)
	}
	got := m.String()
	want := "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RH0LA"
	if got != want {
		t.Fatalf("format %s", got)
	}
	m2, err := Parse("1rb 1lc  1rc 1rb  1rd 0le  1la 1ld  1rh 0la")
	if err != nil {
		t.Fatal(err)
	}
	if m2.String() != want {
		t.Fatalf("whitespace format %s", m2)
	}
}

func TestSearch4LowerBound(t *testing.T) {
	r := Search(4, defaultLimit(4))
	if r.Proved {
		t.Fatal("n=4 fully decided; pin the proved scores before treating them as exact")
	}
	if r.Steps.Steps < 107 || r.Ones.Ones < 13 || r.Space.Space < 16 {
		t.Fatalf("n=4 lower bound S=%d (%s) Σ=%d (%s) space=%d (%s)",
			r.Steps.Steps, r.Steps.Spec, r.Ones.Ones, r.Ones.Spec, r.Space.Space, r.Space.Spec)
	}
	if r.Steps.Spec != "1RB1LB_1LA0LC_1RH1LD_1RD0RA" || r.Ones.Spec != r.Steps.Spec {
		t.Fatalf("n=4 champions steps=%s ones=%s space=%s", r.Steps.Spec, r.Ones.Spec, r.Space.Spec)
	}
}

func TestPhaseEqual(t *testing.T) {
	left := []aseg{
		{wall: true, s: "0"},
		{w: "10", a: 6, b: 2},
		{wall: true, s: "101"},
	}
	right := []aseg{{w: "01", a: 8, b: 2}}
	if !tapesEqual(left, right) {
		t.Fatal("phase-shifted repeater tapes should be equal for every K")
	}
	if tapesEqual([]aseg{{wall: true, s: "1"}}, []aseg{{wall: true, s: "0"}}) {
		t.Fatal("distinct constants compared equal")
	}
}

func TestLoopWitnesses(t *testing.T) {
	bouncers := []string{
		"1RB1LA_1RC1RB_1LA---",
		"1RB1RC_1LC---_0RA0LB",
		"1RB1LA_0LA0LC_---1RA",
		"1RB---_1LB1RC_1LB0RC",
	}
	for _, spec := range bouncers {
		m := mustParse(t, spec)
		o := Decide(m, 8_000)
		if o.Verdict != VerdictLoop || o.Reason != ReasonBounce {
			t.Fatalf("%s: %s (%s)", spec, o.Status(), o.Reason)
		}
		if o.Offset < 1 || (o.Side != "left" && o.Side != "right") {
			t.Fatalf("%s witness offset=%d side=%q", spec, o.Offset, o.Side)
		}
	}
	counters := []string{
		"1RB---_1LC0RB_0LC1RB",
		"1RB---_1LC1RA_0RA0LC",
		"1RB---_1LC1RB_0RA0LC",
		"1RB---_1LC1RB_0RB0LC",
		"1RB1LC_0LA0RB_1LA---",
		"1RB---_0LB1RC_1LB0RC",
		"1RB---_1RC1LB_0LB0RC",
		"1RB---_0RC0LB_1LB1RC",
		"1RB---_0LC0RB_1RB1LC",
	}
	for _, spec := range counters {
		m := mustParse(t, spec)
		o := Decide(m, 8_000)
		if o.Verdict != VerdictLoop || o.Reason != ReasonCounter {
			t.Fatalf("%s: %s (%s)", spec, o.Status(), o.Reason)
		}
	}
}

func TestNoFalseLoop(t *testing.T) {
	// Champions that are still running at this limit must stay unknown.
	// A loop verdict here would be a false proof.
	cases := []struct {
		spec  string
		limit uint64
	}{
		{"1RB1LB_1LA0LC_1RH1LD_1RD0RA", 50},
		{"1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 10_000},
		{"1RB1RH_0RC1RB_1LC1LA", 5},
	}
	for _, c := range cases {
		m := mustParse(t, c.spec)
		o := Decide(m, c.limit)
		if o.Verdict == VerdictLoop {
			t.Fatalf("%s limit %d proved loop (%s)", c.spec, c.limit, o.Reason)
		}
	}
}

func mustParse(t *testing.T, spec string) Machine {
	t.Helper()
	m, err := Parse(spec)
	if err != nil {
		t.Fatal(err)
	}
	return m
}
