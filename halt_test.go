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

func TestProgramEncoding(t *testing.T) {
	ones, err := encode(mustParse(t, "1RH1RH"))
	if err != nil {
		t.Fatal(err)
	}
	if ones != "0111111" || len(ones) != programBits(1) {
		t.Fatalf("1RH1RH encoded %s", ones)
	}
	sweep, err := encode(mustParse(t, "1RA1RA"))
	if err != nil || sweep != "0110110" {
		t.Fatalf("1RA1RA encoded %s %v", sweep, err)
	}
	for _, spec := range []string{
		"1RH1RH",
		"1RA1RA",
		"1RB1LB_1LA1RH",
		"1RB1RH_0RC1RB_1LC1LA",
		"1RB1LB_1LA0LC_1RH1LD_1RD0RA",
		"1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA",
	} {
		m := mustParse(t, spec)
		prog, err := encode(m)
		if err != nil {
			t.Fatalf("%s: %v", spec, err)
		}
		if len(prog) != programBits(m.N) {
			t.Fatalf("%s length %d, want %d", spec, len(prog), programBits(m.N))
		}
		got, err := decode(prog)
		if err != nil {
			t.Fatalf("decode %s: %v", spec, err)
		}
		if got.String() != m.String() {
			t.Fatalf("round trip %s -> %s", m, got)
		}
		if _, err := decode(prog + "0"); err == nil {
			t.Fatalf("%s accepts a trailing bit", spec)
		}
	}
	if _, err := encode(mustParse(t, "1RA")); err == nil {
		t.Fatal("partial table encoded as a program")
	}
	if programWitness("1RH", 1) != "1RH1RH" {
		t.Fatalf("1-state witness %s", programWitness("1RH", 1))
	}
	for i := 0; i < definedProgramCount(1); i++ {
		m := machineFromIndex(1, i)
		prog, err := encode(m)
		if err != nil {
			t.Fatal(err)
		}
		got, err := decode(prog)
		if err != nil || got.String() != m.String() {
			t.Fatalf("index %d round trip %s -> %s %v", i, m, got, err)
		}
	}
}

func TestDecideK(t *testing.T) {
	halt1, err := DecideK(mustParse(t, "1RH1RH"))
	if err != nil || halt1.Verdict != VerdictHalt || halt1.Steps != 1 || !halt1.KExact || halt1.KBits != programBits(1) {
		t.Fatalf("1RH1RH: %+v %v", halt1, err)
	}
	loop1, err := DecideK(mustParse(t, "1RA1RA"))
	if err != nil || loop1.Verdict != VerdictLoop || loop1.Reason != ReasonK || loop1.KBound != 1 {
		t.Fatalf("1RA1RA: %+v %v", loop1, err)
	}
	bb2, err := DecideK(mustParse(t, "1RB1LB_1LA1RH"))
	if err != nil || bb2.Verdict != VerdictHalt || bb2.Steps != 6 || !bb2.KExact || bb2.KBits != programBits(2) {
		t.Fatalf("BB2: %+v %v", bb2, err)
	}

	complexityClasses()
	champ := mustParse(t, kClass[3].Steps.Spec)
	bb3, err := DecideK(champ)
	if err != nil || bb3.Verdict != VerdictHalt || bb3.Steps != kClass[3].Steps.Steps || bb3.Steps != bb3.KBound || !bb3.KExact {
		t.Fatalf("3-state step champion %s: %+v %v", champ, bb3, err)
	}
	sweep3, err := DecideK(mustParse(t, "1RA1RA_1RA1RA_1RA1RA"))
	if err != nil || sweep3.Verdict != VerdictLoop || sweep3.Reason != ReasonK || sweep3.KBound != bb3.KBound {
		t.Fatalf("3-state sweep: %+v %v", sweep3, err)
	}

	// The 4-state cutoff is not proved. A halt is still a witness.
	// A machine that is still running must stay unknown.
	bb4, err := DecideK(mustParse(t, "1RB1LB_1LA0LC_1RH1LD_1RD0RA"))
	if err != nil || bb4.Verdict != VerdictHalt || bb4.Steps != 107 || bb4.KExact || bb4.Reason == ReasonK {
		t.Fatalf("BB4: %+v %v", bb4, err)
	}
	open4, err := DecideK(mustParse(t, "1RA1RA_1RA1RA_1RA1RA_1RA1RA"))
	if err != nil || open4.Verdict != VerdictUnknown || open4.Reason != ReasonK {
		t.Fatalf("4-state sweep: %+v %v", open4, err)
	}
	if _, err := DecideK(mustParse(t, "1RA")); err == nil {
		t.Fatal("partial machine was decided by the cutoff")
	}
}

func TestKBoundMatchesTables(t *testing.T) {
	for n := 1; n <= 2; n++ {
		bound, ok := stepCutoff(n)
		if !ok {
			t.Fatalf("n=%d cutoff not proved", n)
		}
		got := maxDefinedHalt(n, bound+50)
		if got != bound {
			t.Fatalf("n=%d complete programs halt in at most %d steps, cutoff %d", n, got, bound)
		}
	}
}

func TestDecideStat(t *testing.T) {
	for _, c := range Champions {
		m := mustParse(t, c.Spec)
		o := DecideStat(m, c.Steps)
		if o.Verdict != VerdictHalt || o.Steps != c.Steps || o.Ones != c.Ones {
			t.Fatalf("BB(%d) %s: %s steps=%d ones=%d reason=%s, want halt steps=%d ones=%d",
				c.N, c.Spec, o.Status(), o.Steps, o.Ones, o.Reason, c.Steps, c.Ones)
		}
	}

	// A short run of a real halter is unknown. A loop here would be a false proof.
	open := []struct {
		spec  string
		limit uint64
	}{
		{"1RB1LB_1LA1RH", 4},
		{"1RB1LB_1LA1RH", 5},
		{"1RB1LB_1LA0LC_1RH1LD_1RD0RA", 50},
		{"1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA", 10_000},
		{"1RB1RH_0RC1RB_1LC1LA", 5},
		// Undefined halt at step 2. limit 2 stops before that read.
		{"0RB1RA_0LC1RA_---1LA", 2},
		// Skelet #10. An earlier backward-reasoning implementation closed
		// this machine unsoundly. The tree is still open inside our caps.
		{"1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB", 100},
	}
	for _, c := range open {
		m := mustParse(t, c.spec)
		o := DecideStat(m, c.limit)
		if o.Verdict == VerdictLoop {
			t.Fatalf("%s limit %d proved loop (%s depth %d)", c.spec, c.limit, o.Reason, o.StatDepth)
		}
	}

	bb2 := DecideStat(mustParse(t, "1RB1LB_1LA1RH"), 6)
	if bb2.Verdict != VerdictHalt || bb2.Steps != 6 || bb2.Ones != 4 {
		t.Fatalf("BB2 at 6: %+v", bb2)
	}
	if bb2.StatLine != "A0 x 2 B0 x 2 A1 x 1 B1 x 1" && bb2.StatLine != "B0 x 2 A0 x 2 A1 x 1 B1 x 1" {
		// A0 and B0 tie at 2. The mode scan keeps the earlier state.
		t.Fatalf("BB2 reads %q", bb2.StatLine)
	}
	if bb2.StatState != 0 || bb2.StatSym != 0 || bb2.StatCount != 2 || bb2.StatReads != 6 {
		t.Fatalf("BB2 mode state=%d sym=%d count=%d reads=%d", bb2.StatState, bb2.StatSym, bb2.StatCount, bb2.StatReads)
	}

	early := DecideStat(mustParse(t, "1RB1LB_1LA1RH"), 4)
	if early.Verdict != VerdictUnknown || early.Reason != ReasonStat || early.Steps != 4 {
		t.Fatalf("BB2 at 4: %s %s steps=%d", early.Status(), early.Reason, early.Steps)
	}
	if early.StatLine != "B0 x 2 A0 x 1 A1 x 1" {
		t.Fatalf("BB2 early reads %q", early.StatLine)
	}

	halt1 := DecideStat(mustParse(t, "1RH"), 10)
	if halt1.Verdict != VerdictHalt || halt1.Steps != 1 || halt1.Reason != ReasonHalt {
		t.Fatalf("1RH: %+v", halt1)
	}
	blank := DecideStat(mustParse(t, "------"), 10)
	if blank.Verdict != VerdictHalt || blank.Steps != 0 || blank.Reason != ReasonUndefined {
		t.Fatalf("------: %+v", blank)
	}

	// B's halt is unreachable. The blank tape never leaves A.
	dead := DecideStat(mustParse(t, "1RA1RA_1RH1RH"), 10)
	if dead.Verdict != VerdictLoop || dead.Reason != ReasonStat || dead.StatDepth != 0 {
		t.Fatalf("dead halt: %+v", dead)
	}
	sweep := DecideStat(mustParse(t, "1RA1RA"), 10)
	if sweep.Verdict != VerdictLoop || sweep.Reason != ReasonStat || sweep.StatDepth != -1 {
		t.Fatalf("1RA1RA: %+v", sweep)
	}
	if sweep.StatState != 0 || sweep.StatSym != 0 || sweep.StatCount != 10 || sweep.StatReads != 10 || sweep.StatLine != "A0 x 10" {
		t.Fatalf("1RA1RA reads state=%d sym=%d count=%d total=%d line=%q",
			sweep.StatState, sweep.StatSym, sweep.StatCount, sweep.StatReads, sweep.StatLine)
	}

	// The only halt reads 0 in C. Reaching it requires a 0 that the
	// previous step wrote as a 1. Depth 1 closes the tree.
	contra := mustParse(t, "1RB1RA_0LC1RA_---1LA")
	if got := DecideStat(contra, 1); got.Verdict == VerdictLoop {
		t.Fatalf("contradiction machine looped at limit 1, depth %d", got.StatDepth)
	}
	got := DecideStat(contra, 2)
	if got.Verdict != VerdictLoop || got.Reason != ReasonStat || got.StatDepth != 1 || got.Period != 2 {
		t.Fatalf("contradiction machine: %s %s depth=%d nodes=%d", got.Status(), got.Reason, got.StatDepth, got.Period)
	}
	sim := Simulate(contra, 100_000)
	if sim.Verdict == VerdictHalt {
		t.Fatalf("contradiction machine halted at step %d", sim.Steps)
	}

	late := DecideStat(mustParse(t, "0RB1RA_0LC1RA_---1LA"), 3)
	if late.Verdict != VerdictHalt || late.Steps != 2 || late.Reason != ReasonUndefined {
		t.Fatalf("matching write: %+v", late)
	}
}

func maxDefinedHalt(n int, limit uint64) uint64 {
	e := newEngine()
	var max uint64
	count := definedProgramCount(n)
	for i := 0; i < count; i++ {
		m := machineFromIndex(n, i)
		e.load(m)
		e.limit = limit
		e.detect = false
		e.wantTape = false
		e.reset()
		o := e.exec()
		if o.Verdict == VerdictHalt && o.Steps > max {
			max = o.Steps
		}
	}
	return max
}

func mustParse(t *testing.T, spec string) Machine {
	t.Helper()
	m, err := Parse(spec)
	if err != nil {
		t.Fatal(err)
	}
	return m
}
