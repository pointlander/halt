// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"flag"
	"fmt"
	"os"
	"strconv"
	"strings"
	"time"
)

func main() {
	if len(os.Args) < 2 {
		demo()
		return
	}
	switch os.Args[1] {
	case "decide":
		cmdDecide(os.Args[2:])
	case "run":
		cmdRun(os.Args[2:])
	case "search":
		cmdSearch(os.Args[2:])
	case "k":
		cmdK(os.Args[2:])
	case "stat":
		cmdStat(os.Args[2:])
	case "tree":
		cmdTree(os.Args[2:])
	case "help", "-h", "--help":
		usage()
	default:
		usage()
		os.Exit(2)
	}
}

func usage() {
	fmt.Fprintf(os.Stderr, `halt — a partial Turing-machine halting decider

The blank-tape halting problem is undecidable. halt proves the cases it can
and says "unknown" otherwise. Busy beaver champions are the worked example:
S(n) is the longest a halting n-state 2-symbol machine can run, and Σ(n) is
the most 1s one can leave. Both are uncomputable, and known exactly through n = 5.

Usage:
  halt                         simulate champions and compute S(n), Σ(n) for small n
  halt run SPEC [--trace]      simulate one machine (a halt is a witness)
  halt decide SPEC [--limit N] prove halt or loop, or report unknown
  halt search N [--limit N]    search n-state machines for S(n) and Σ(n)
  halt k                       program-size cutoff for short programs
  halt k decide SPEC           decide SPEC by that cutoff
  halt stat                    backward and forward state-symbol search
  halt stat decide SPEC [--limit N]
                               decide SPEC by that search
  halt tree                    tree-calculus reduction search
  halt tree decide TERM [--limit N]
                               decide TERM by that search

SPEC is standard text format, for example 1RB1LB_1LA1RH.
H and Z both mean halt. --- is an undefined transition.
The k command requires a complete table: every transition is defined.
A tree term uses ^ for the leaf. Application is juxtaposition and
associates to the left. Parentheses group. △ and Δ are also the leaf.
`)
}

func cmdRun(args []string) {
	fs := flag.NewFlagSet("run", flag.ExitOnError)
	limit := fs.Uint64("limit", 0, "maximum steps (0 selects a default)")
	trace := fs.Bool("trace", false, "print every configuration")
	fs.Parse(args)
	spec := strings.Join(fs.Args(), "")
	m, err := Parse(spec)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}
	lim := *limit
	if lim == 0 {
		lim = defaultLimit(m.N)
	}
	if *trace {
		o, steps := Trace(m, lim)
		for _, st := range steps {
			fmt.Printf("%6d  %s  %s\n", st.N, st.State, st.Tape)
		}
		printOutcome(m.String(), o)
		return
	}
	o := Simulate(m, lim)
	printOutcome(m.String(), o)
}

func cmdDecide(args []string) {
	fs := flag.NewFlagSet("decide", flag.ExitOnError)
	limit := fs.Uint64("limit", 0, "maximum steps (0 selects a default)")
	fs.Parse(args)
	spec := strings.Join(fs.Args(), "")
	m, err := Parse(spec)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}
	lim := *limit
	if lim == 0 {
		lim = defaultLimit(m.N)
	}
	o := Decide(m, lim)
	printOutcome(m.String(), o)
}

func cmdSearch(args []string) {
	fs := flag.NewFlagSet("search", flag.ExitOnError)
	limit := fs.Uint64("limit", 0, "maximum steps per machine (0 selects a default)")
	fs.Parse(args)
	if fs.NArg() != 1 {
		usage()
		os.Exit(2)
	}
	n, err := strconv.Atoi(fs.Arg(0))
	if err != nil || n < 1 || n > 6 {
		fmt.Fprintf(os.Stderr, "n must be from 1 to 6\n")
		os.Exit(1)
	}
	lim := *limit
	if lim == 0 {
		lim = defaultLimit(n)
	}
	start := time.Now()
	r := Search(n, lim)
	printSearch(r, time.Since(start))
}

func cmdK(args []string) {
	if len(args) == 0 {
		printComplexity()
		return
	}
	if args[0] != "decide" {
		usage()
		os.Exit(2)
	}
	spec := strings.Join(args[1:], "")
	m, err := Parse(spec)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}
	o, err := DecideK(m)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		os.Exit(1)
	}
	printKDecision(m, o)
}

func printComplexity() {
	fmt.Print(`Program-size complexity
  Programs for the reference machine U are prefix-free encodings of complete
  transition tables. U(p) is how many steps p runs on a blank tape. If p
  halts in t steps, then K(t) is at most the length of p, so an L-bit program
  halts within Σ_H(L) steps or not at all. Σ_H(L) is proved here only for
  programs of at most 3 states, because only those classes are fully decided.
  A machine past that line can still be seen to halt, but a run that is still
  going is unknown: a lower bound on Σ_H is not a cutoff.

`)
	var prev uint64
	for n := 1; n <= 3; n++ {
		complexityClasses()
		r := kClass[n]
		kind := "proved"
		if !r.Proved {
			kind = "not proved"
		}
		fmt.Printf("  n=%d  %d bits  Σ_H=%s  %s\n", n, programBits(n), comma(r.Steps.Steps), kind)
		if r.Proved && r.Steps.Steps > prev {
			fmt.Printf("        K(%s) = %d   witness %s\n",
				comma(r.Steps.Steps), programBits(n), programWitness(r.Steps.Spec, r.Steps.Steps))
			prev = r.Steps.Steps
		}
	}
	fmt.Printf("  n≥4  %d bits and up  Σ_H not proved\n", programBits(4))

	fmt.Println("\nDecisions from the cutoff")
	specs := []string{"1RH1RH", "1RA1RA", "1RB1LB_1LA1RH"}
	if kClass[3].Steps.Spec != "" {
		specs = append(specs, kClass[3].Steps.Spec)
	}
	specs = append(specs, "1RA1RA_1RA1RA_1RA1RA", "1RB1LB_1LA0LC_1RH1LD_1RD0RA")
	for _, spec := range specs {
		m, err := Parse(spec)
		if err != nil {
			fmt.Printf("  %s  parse error: %v\n", spec, err)
			continue
		}
		o, err := DecideK(m)
		if err != nil {
			fmt.Printf("  %s  %v\n", spec, err)
			continue
		}
		printKDecision(m, o)
	}
}

func cmdStat(args []string) {
	if len(args) == 0 {
		printStat()
		return
	}
	if args[0] != "decide" {
		usage()
		os.Exit(2)
	}
	fs := flag.NewFlagSet("stat", flag.ExitOnError)
	limit := fs.Uint64("limit", 0, "maximum steps (0 selects a default)")
	// endFlags keeps a machine such as ------ from being read as a flag.
	fs.Parse(endFlags(args[1:]))
	spec := strings.Join(fs.Args(), "")
	m, err := Parse(spec)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}
	lim := *limit
	if lim == 0 {
		lim = defaultLimit(m.N)
	}
	printStatDecision(m, DecideStat(m, lim))
}

func printStat() {
	fmt.Print(`State-symbol search
  Forward, every read is counted by state and symbol. Backward, each
  halting read is the root of a tree of partial tapes. A reverse step
  stands when the cell it wrote is still unknown or already holds that
  write. If every branch contradicts by depth H, a halt occurs by step
  H+1. A blank-tape run that has already passed that step is a loop
  proof. The counts choose which branch to expand first. Every branch
  is still expanded. A tree that hits the depth cap or the node cap is unknown.

`)
	samples := []struct {
		spec  string
		limit uint64
	}{
		{"1RA1RA_1RH1RH", 32},
		{"1RB1RA_0LC1RA_---1LA", 32},
		{"1RB1LB_1LA1RH", 32},
		{"1RB1LB_1LA1RH", 4},
	}
	for _, s := range samples {
		m, err := Parse(s.spec)
		if err != nil {
			fmt.Printf("  %s  parse error: %v\n", s.spec, err)
			continue
		}
		printStatDecision(m, DecideStat(m, s.limit))
	}
}

func cmdTree(args []string) {
	if len(args) == 0 {
		printTree()
		return
	}
	if args[0] != "decide" {
		usage()
		os.Exit(2)
	}
	fs := flag.NewFlagSet("tree", flag.ExitOnError)
	limit := fs.Uint64("limit", 0, "maximum parallel-outermost steps (0 selects a default)")
	fs.Parse(args[1:])
	spec := strings.Join(fs.Args(), " ")
	term, err := ParseTree(spec)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse: %v\n", err)
		os.Exit(1)
	}
	printTreeDecision(term.String(), DecideTree(term, treeCap(*limit)))
}

func treeCap(limit uint64) int {
	if limit == 0 {
		return treeStepCap
	}
	if limit > uint64(treeStepCapMax) {
		return treeStepCapMax
	}
	return int(limit)
}

func printTree() {
	fmt.Print(`Tree calculus
  A term is a leaf or the application of two terms. Five triage rules
  reduce it: △ △ y z becomes y, △ (△ x) y z becomes x z (y z), and a
  fork △ (△ w x) y applied to a leaf, a stem, or a fork selects w, x,
  or y. The search contracts every outermost redex together. A value is
  a halt witness. ω ω does not halt: a block is ω, I on a block, or K
  on a block applied to K on a block, and applying two blocks only
  produces more of those applications. K leaf (ω ω) halts, because that
  rule discards the copy. A search that hits the step cap is unknown.
  No term decides halting for every term.

`)
	k := treeK()
	w := treeOmega()
	samples := []struct {
		name string
		term *treeTerm
	}{
		{"leaf", tLeaf()},
		{"not false", tApp(treeNot(), tLeaf())},
		{"not true", tApp(treeNot(), k)},
		{"K leaf (ω ω)", tApp(tApp(k, tLeaf()), tApp(w, w))},
		{"ω ω", tApp(w, w)},
	}
	for _, s := range samples {
		fmt.Printf("  %s\n    %s\n    %s\n", s.name, s.term, DecideTree(s.term, 0).Text())
	}
}

func printTreeDecision(spec string, r TreeResult) {
	fmt.Printf("  %s\n    %s\n", spec, r.Text())
}

func printStatDecision(m Machine, o Outcome) {
	fmt.Printf("  %s\n    %s\n", m, describe(o))
	if o.StatLine != "" {
		fmt.Printf("    reads %s\n", o.StatLine)
	}
	if o.Tape != "" && o.Verdict == VerdictHalt && m.N <= 4 {
		fmt.Printf("    tape %s\n", o.Tape)
	}
}

func printKDecision(m Machine, o Outcome) {
	fmt.Printf("  %s\n    %s\n", m, describe(o))
	if o.Verdict == VerdictHalt && o.KBits > 0 {
		op := "≤"
		if o.KExact {
			op = "="
		}
		fmt.Printf("    K(%s) %s %d\n", comma(o.Steps), op, o.KBits)
	}
	if o.Tape != "" && m.N <= 4 {
		fmt.Printf("    tape %s\n", o.Tape)
	}
}

func demo() {
	fmt.Print(`A Turing machine, started on a blank tape, either halts or runs forever.
No algorithm answers that for every machine. That is the halting problem.
The busy beaver function S(n) — the longest a halting n-state 2-symbol
machine can run — grows faster than any computable function, because a
way to compute it would decide the blank-tape halting problem.

This program is a partial decider. A halt verdict is a simulation witness.
A loop verdict is a proof: a configuration repeated (a cycler), a
record-breaking configuration repeated shifted in space (a translated
cycler), the reachable transitions are all defined and none of them halts,
a bouncer that inserts one more copy of a block on every pass, or a binary
counter that adds one cell each time it overflows.
Unknown means the step bound ran out before any of those proofs.

`)
	fmt.Println("Loop proofs")
	for _, spec := range []string{"1RA", "0RB1RH_0LA1RH"} {
		m, err := Parse(spec)
		if err != nil {
			fmt.Printf("  %s  parse error: %v\n", spec, err)
			continue
		}
		o := Decide(m, 10_000)
		fmt.Printf("  %s\n", m)
		fmt.Printf("    %s\n", describe(o))
	}

	fmt.Println("\nBusy beaver champions, blank tape")
	for _, c := range Champions {
		m, err := Parse(c.Spec)
		if err != nil {
			fmt.Printf("  BB(%d) parse error: %v\n", c.N, err)
			continue
		}
		start := time.Now()
		o := Simulate(m, c.Steps+10)
		dt := time.Since(start)
		ok := o.Verdict == VerdictHalt && o.Steps == c.Steps && o.Ones == c.Ones
		mark := "ok"
		if !ok {
			mark = "MISMATCH"
		}
		fmt.Printf("  BB(%d)  %-40s  %s\n", c.N, m, mark)
		fmt.Printf("        steps %-12s  ones %-8s  space %-8s  %s\n",
			comma(o.Steps), comma(uint64(o.Ones)), comma(uint64(o.Space)), dt.Round(time.Millisecond))
		if o.Tape != "" && c.N <= 4 {
			fmt.Printf("        tape %s\n", o.Tape)
		}
	}

	fmt.Println("\nSearch in tree normal form")
	fmt.Println("  First transition fixed to 1RB for n > 1. Mirrors and state relabelings are omitted.")
	for n := 1; n <= 4; n++ {
		lim := defaultLimit(n)
		start := time.Now()
		r := Search(n, lim)
		printSearch(r, time.Since(start))
	}
	fmt.Println()
	printComplexity()
	fmt.Println()
	printStat()
	fmt.Println()
	printTree()
}

func printOutcome(spec string, o Outcome) {
	fmt.Printf("%s\n  %s\n", spec, describe(o))
	if o.Tape != "" {
		fmt.Printf("  tape %s\n", o.Tape)
	}
}

func describe(o Outcome) string {
	switch o.Verdict {
	case VerdictHalt:
		how := "halting transition"
		if o.Reason == ReasonUndefined {
			how = "undefined transition, no write"
		}
		return fmt.Sprintf("halts at step %s by %s, %s ones, space %s",
			comma(o.Steps), how, comma(uint64(o.Ones)), comma(uint64(o.Space)))
	case VerdictLoop:
		switch o.Reason {
		case ReasonTranslated:
			return fmt.Sprintf("does not halt: translated cycler, %s shift %d, period %s, from step %s",
				o.Side, o.Offset, comma(o.Period), comma(o.Start))
		case ReasonNoHalt:
			return "does not halt: every reachable transition is defined and none halts"
		case ReasonBounce:
			return fmt.Sprintf("does not halt: bouncer, grows by %d cells each pass on the %s",
				o.Offset, o.Side)
		case ReasonCounter:
			return "does not halt: binary counter, adds one cell each time the counter overflows"
		case ReasonK:
			return fmt.Sprintf("does not halt: a %d-bit program halts within %s %s or not at all",
				o.KBits, comma(o.KBound), stepsWord(o.KBound))
		case ReasonStat:
			if o.StatDepth < 0 {
				return "does not halt: no transition halts"
			}
			if o.StatDepth == 0 {
				return fmt.Sprintf("does not halt: nothing reaches a halting read, and the blank tape ran %s %s",
					comma(o.Steps), stepsWord(o.Steps))
			}
			return fmt.Sprintf("does not halt: every path to a halting read contradicts by depth %d, and the blank tape ran %s %s",
				o.StatDepth, comma(o.Steps), stepsWord(o.Steps))
		}
		return fmt.Sprintf("does not halt: cycler, period %s, from step %s",
			comma(o.Period), comma(o.Start))
	default:
		if o.Reason == ReasonK {
			return fmt.Sprintf("unknown: no proved K cutoff for a %d-bit program (ran %s %s)",
				o.KBits, comma(o.Steps), stepsWord(o.Steps))
		}
		if o.Reason == ReasonStat {
			return describeStatUnknown(o)
		}
		return fmt.Sprintf("unknown after %s steps (%s)", comma(o.Steps), o.Reason)
	}
}

func describeStatUnknown(o Outcome) string {
	if o.Period > uint64(statNodeCap) {
		return fmt.Sprintf("unknown: backward search hit the node cap at depth %d (%s nodes, ran %s %s)",
			o.StatDepth, comma(o.Period), comma(o.Steps), stepsWord(o.Steps))
	}
	return fmt.Sprintf("unknown: backward search stopped at depth %d (%s nodes, ran %s %s)",
		o.StatDepth, comma(o.Period), comma(o.Steps), stepsWord(o.Steps))
}

// endFlags inserts "--" before the machine, so a spec of dashes is an
// argument and a limit flag placed in front of it still parses.
func endFlags(args []string) []string {
	var out []string
	for i := 0; i < len(args); i++ {
		a := args[i]
		if a == "--" {
			return append(out, args[i:]...)
		}
		if a == "-limit" || a == "--limit" {
			out = append(out, a)
			if i+1 < len(args) {
				i++
				out = append(out, args[i])
			}
			continue
		}
		out = append(out, "--")
		out = append(out, args[i:]...)
		return out
	}
	return out
}

func printSearch(r SearchResult, dt time.Duration) {
	kind := "proved"
	if !r.Proved {
		kind = "lower bound"
	}
	fmt.Printf("  n=%d  %s  S=%s  Σ=%s  space=%s  (%s)\n",
		r.N, kind, comma(r.Steps.Steps), comma(uint64(r.Ones.Ones)), comma(uint64(r.Space.Space)),
		dt.Round(time.Millisecond))
	fmt.Printf("        leaves  halt %s  loop %s  unknown %s  nodes %s  limit %s\n",
		comma(uint64(r.Halted)), comma(uint64(r.Looping)), comma(uint64(r.Unknown)),
		comma(uint64(r.Nodes)), comma(r.Limit))
	if r.Steps.Spec != "" {
		fmt.Printf("        steps  %s\n", r.Steps.Spec)
	}
	if r.Ones.Spec != "" && r.Ones.Spec != r.Steps.Spec {
		fmt.Printf("        ones   %s\n", r.Ones.Spec)
	}
	if r.Space.Spec != "" && r.Space.Spec != r.Steps.Spec && r.Space.Spec != r.Ones.Spec {
		fmt.Printf("        space  %s\n", r.Space.Spec)
	}
	if !r.Proved && len(r.Open) > 0 {
		fmt.Printf("        open   %s\n", r.Open[0])
	}
}

func defaultLimit(n int) uint64 {
	switch {
	case n <= 1:
		return 100
	case n == 2:
		return 1_000
	case n == 3:
		return 10_000
	case n == 4:
		// Raising this another 10× does not decide any further machine with
		// the current provers; it only re-simulates the ones left open.
		// Crossing the cap is reported as Unknown, never as a loop.
		return 1_000
	default:
		return 50_000_000
	}
}

func stepsWord(n uint64) string {
	if n == 1 {
		return "step"
	}
	return "steps"
}

func encodable(m Machine) bool {
	_, err := encode(m)
	return err == nil
}

// programWitness is a complete program that halts in steps.
// Search may leave an unread transition undefined; filling those with 1RH
// keeps the blank-tape run when the gap was never used.
func programWitness(spec string, steps uint64) string {
	m, err := Parse(spec)
	if err != nil {
		return spec
	}
	if encodable(m) {
		return m.String()
	}
	filled := m
	filled.T = make([][2]Trans, m.N)
	copy(filled.T, m.T)
	for s := 0; s < filled.N; s++ {
		for sym := 0; sym < 2; sym++ {
			if !filled.T[s][sym].Def {
				filled.T[s][sym] = Trans{Write: 1, Dir: 1, Next: -1, Def: true}
			}
		}
	}
	o := Simulate(filled, steps)
	if o.Verdict == VerdictHalt && o.Steps == steps && encodable(filled) {
		return filled.String()
	}
	if w, ok := completeWitness(m.N, steps); ok {
		return w.String()
	}
	return spec
}

func comma(n uint64) string {
	s := strconv.FormatUint(n, 10)
	if len(s) <= 3 {
		return s
	}
	var b strings.Builder
	pre := len(s) % 3
	if pre == 0 {
		pre = 3
	}
	b.WriteString(s[:pre])
	for i := pre; i < len(s); i += 3 {
		b.WriteByte(',')
		b.WriteString(s[i : i+3])
	}
	return b.String()
}
