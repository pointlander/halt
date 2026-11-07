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

SPEC is standard text format, for example 1RB1LB_1LA1RH.
H and Z both mean halt. --- is an undefined transition.
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
		}
		return fmt.Sprintf("does not halt: cycler, period %s, from step %s",
			comma(o.Period), comma(o.Start))
	default:
		return fmt.Sprintf("unknown after %s steps (%s)", comma(o.Steps), o.Reason)
	}
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
