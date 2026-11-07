// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"math/bits"
	"sync"
)

// Program-size complexity is measured on one fixed machine U.
// A program is a prefix-free encoding of a complete n-state 2-symbol table,
// and U(p) is the number of steps that table runs on a blank tape before its
// halting transition. On this U the additive constant in the invariance
// theorem is zero: if p halts in t steps then the complexity K(t) is at most
// the bit length of p.
//
// Σ_H(L) is the largest integer with K ≤ L, which is the longest run of any
// program of length at most L. Chaitin's lemma is then immediate: an L-bit
// program either halts within Σ_H(L) steps or never halts. The cutoff is a
// proof only when every program that short has been decided. A lower bound
// on Σ_H is not a cutoff, and this file never treats one as a loop proof.

// nextFieldBits is the width of the next-state field: ceil(log2(n+1)).
// Values 0..n-1 are states. Value n, and any spare code above it, means halt.
func nextFieldBits(n int) int {
	return bits.Len(uint(n))
}

// programBits is the length of every complete n-state program.
// The state count is written in unary, then each of the 2n transitions.
func programBits(n int) int {
	return n + 2*n*(2+nextFieldBits(n))
}

// encode writes m as a program for U.
// Undefined transitions are not programs: a halting transition has to say
// what it writes and which way it moves.
func encode(m Machine) (string, error) {
	if m.N < 1 || m.N > maxStates || len(m.T) < m.N {
		return "", fmt.Errorf("cannot encode a %d-state machine", m.N)
	}
	nb := nextFieldBits(m.N)
	var b []byte
	for i := 1; i < m.N; i++ {
		b = append(b, '1')
	}
	b = append(b, '0')
	for s := 0; s < m.N; s++ {
		for sym := 0; sym < 2; sym++ {
			tr := m.T[s][sym]
			if !tr.Def {
				return "", fmt.Errorf("%s is not a complete program", m)
			}
			if tr.Write > 1 || (tr.Dir != -1 && tr.Dir != 1) {
				return "", fmt.Errorf("%s has a bad transition", m)
			}
			b = append(b, '0'+tr.Write)
			if tr.Dir < 0 {
				b = append(b, '0')
			} else {
				b = append(b, '1')
			}
			val := int(tr.Next)
			if val < 0 {
				val = m.N
			}
			if val < 0 || val > m.N {
				return "", fmt.Errorf("%s has a bad next state", m)
			}
			for i := nb - 1; i >= 0; i-- {
				bit := byte('0')
				if val&(1<<uint(i)) != 0 {
					bit = '1'
				}
				b = append(b, bit)
			}
		}
	}
	return string(b), nil
}

// decode reads one program. Extra or missing bits are rejected, so no
// program is a prefix of another.
func decode(prog string) (Machine, error) {
	i := 0
	n := 1
	for i < len(prog) && prog[i] == '1' {
		n++
		i++
		if n > maxStates {
			return Machine{}, fmt.Errorf("program has too many states")
		}
	}
	if i >= len(prog) || prog[i] != '0' {
		return Machine{}, fmt.Errorf("program is missing its state-count mark")
	}
	i++
	nb := nextFieldBits(n)
	m := Machine{N: n, T: make([][2]Trans, n)}
	for s := 0; s < n; s++ {
		for sym := 0; sym < 2; sym++ {
			if i+2+nb > len(prog) {
				return Machine{}, fmt.Errorf("program ended inside a transition")
			}
			if prog[i] != '0' && prog[i] != '1' {
				return Machine{}, fmt.Errorf("program has a non-bit")
			}
			write := prog[i] - '0'
			i++
			var dir int8 = 1
			switch prog[i] {
			case '0':
				dir = -1
			case '1':
				dir = 1
			default:
				return Machine{}, fmt.Errorf("program has a non-bit")
			}
			i++
			val := 0
			for bit := 0; bit < nb; bit++ {
				val <<= 1
				switch prog[i] {
				case '0':
				case '1':
					val++
				default:
					return Machine{}, fmt.Errorf("program has a non-bit")
				}
				i++
			}
			next := int8(val)
			if val >= n {
				next = -1
			}
			m.T[s][sym] = Trans{Write: write, Dir: dir, Next: next, Def: true}
		}
	}
	if i != len(prog) {
		return Machine{}, fmt.Errorf("program has %d trailing bits", len(prog)-i)
	}
	return m, nil
}

// machineFromIndex lists complete n-state tables, including the spare
// halt codes in the next-state field. Those aliases repeat a machine.
func machineFromIndex(n, index int) Machine {
	nb := nextFieldBits(n)
	width := 2 + nb
	mask := (1 << uint(width)) - 1
	m := Machine{N: n, T: make([][2]Trans, n)}
	for s := 0; s < n; s++ {
		for sym := 0; sym < 2; sym++ {
			chunk := index & mask
			index >>= uint(width)
			dir := int8(1)
			if (chunk>>1)&1 == 0 {
				dir = -1
			}
			val := chunk >> 2
			next := int8(val)
			if val >= n {
				next = -1
			}
			m.T[s][sym] = Trans{Write: byte(chunk & 1), Dir: dir, Next: next, Def: true}
		}
	}
	return m
}

// definedProgramCount is the number of bitstrings machineFromIndex walks.
func definedProgramCount(n int) int {
	return 1 << uint(2*n*(2+nextFieldBits(n)))
}

// completeWitness returns one complete program whose blank-tape run
// halts in exactly steps. The search can score the same run with an
// undefined transition left over; that table is not a program for U.
func completeWitness(n int, steps uint64) (Machine, bool) {
	if n < 1 || n > 2 {
		return Machine{}, false
	}
	e := newEngine()
	count := definedProgramCount(n)
	for i := 0; i < count; i++ {
		m := machineFromIndex(n, i)
		e.load(m)
		e.limit = steps
		e.detect = false
		e.wantTape = false
		e.reset()
		o := e.exec()
		if o.Verdict == VerdictHalt && o.Steps == steps {
			return m, true
		}
	}
	return Machine{}, false
}

var (
	kOnce  sync.Once
	kClass [4]SearchResult
)

// complexityClasses decides every machine of 1, 2, and 3 states.
// The results are cached. Search never consults the cutoff, so the
// bound does not depend on itself.
func complexityClasses() {
	kOnce.Do(func() {
		for n := 1; n <= 3; n++ {
			kClass[n] = Search(n, defaultLimit(n))
		}
	})
}

// stepCutoff is Σ_H for programs of at most n states, when that value is proved.
// It is the longest blank-tape run of any decided machine with ≤ n states.
func stepCutoff(n int) (uint64, bool) {
	if n < 1 || n > 3 {
		return 0, false
	}
	complexityClasses()
	var max uint64
	for i := 1; i <= n; i++ {
		if !kClass[i].Proved {
			return 0, false
		}
		if kClass[i].Steps.Steps > max {
			max = kClass[i].Steps.Steps
		}
	}
	return max, true
}

// DecideK applies Chaitin's lemma to one complete machine.
// Halt is a simulation witness inside the proved cutoff.
// Loop means the run is still going at Σ_H, so the halting time would be an
// integer more complex than every integer the short programs can name.
// When the cutoff is not proved the lemma does not apply: a halt is still a
// witness, and anything still running is unknown.
func DecideK(m Machine) (Outcome, error) {
	if _, err := encode(m); err != nil {
		return Outcome{}, err
	}
	bits := programBits(m.N)
	bound, proved := stepCutoff(m.N)
	if !proved {
		o := Simulate(m, defaultLimit(m.N))
		o.KBits = bits
		if o.Verdict == VerdictHalt {
			return o, nil
		}
		o.Verdict = VerdictUnknown
		o.Reason = ReasonK
		return o, nil
	}
	o := Simulate(m, bound)
	o.KBits = bits
	o.KBound = bound
	if o.Verdict == VerdictHalt && o.Steps <= bound {
		var prev uint64
		if m.N > 1 {
			prev, _ = stepCutoff(m.N - 1)
		}
		o.KExact = o.Steps > prev
		return o, nil
	}
	o.Verdict = VerdictLoop
	o.Reason = ReasonK
	return o, nil
}
