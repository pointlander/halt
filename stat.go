// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"sort"
	"strings"
)

// Bidirectional state-symbol search.
//
// Forward, the machine is run from a blank tape and every read is counted
// by state and symbol. Backward, every halting read (an undefined transition
// or an explicit halt) is the root of a tree of partial tapes. A reverse step
// undoes one transition: the head came from the opposite direction, and the
// cell it left must carry that transition's write. If the cell is already
// known and differs, the branch is impossible.
//
// If every branch contradicts by depth H, a halting read is reachable in at
// most H steps, so the halt itself happens by step H+1. A blank-tape run of
// H+1 steps that does not halt therefore never does. The forward counts
// choose which reverse branch to expand first. They never delete a branch;
// a rare state can still be the one that halts.

const (
	statMaxDepth = 32
	statNodeCap  = 100_000
)

type statTape map[int]byte

type statNode struct {
	state  int
	head   int
	lo, hi int
	depth  int
	tape   statTape
}

type statHist struct {
	read [maxStates][2]uint64
	rev  [maxStates][2]uint64
}

func (h statHist) total() uint64 {
	var n uint64
	for s := 0; s < maxStates; s++ {
		n += h.read[s][0] + h.read[s][1]
	}
	return n
}

func (h statHist) mode() (state, sym int, count uint64) {
	for s := 0; s < maxStates; s++ {
		for b := 0; b < 2; b++ {
			if h.read[s][b] > count {
				state, sym, count = s, b, h.read[s][b]
			}
		}
	}
	return state, sym, count
}

func (h statHist) weight(state, sym int) uint64 {
	if state < 0 || state >= maxStates || sym < 0 || sym > 1 {
		return 0
	}
	return h.read[state][sym]
}

// line lists nonzero forward counts, most common first.
func (h statHist) line() string {
	type bin struct {
		state int
		sym   int
		n     uint64
	}
	var bins []bin
	for s := 0; s < maxStates; s++ {
		for sym := 0; sym < 2; sym++ {
			if h.read[s][sym] == 0 {
				continue
			}
			bins = append(bins, bin{s, sym, h.read[s][sym]})
		}
	}
	sort.Slice(bins, func(i, j int) bool {
		if bins[i].n != bins[j].n {
			return bins[i].n > bins[j].n
		}
		if bins[i].state != bins[j].state {
			return bins[i].state < bins[j].state
		}
		return bins[i].sym < bins[j].sym
	})
	var b strings.Builder
	for i, bin := range bins {
		if i > 0 {
			b.WriteByte(' ')
		}
		fmt.Fprintf(&b, "%s%d x %d", stateName(bin.state), bin.sym, bin.n)
	}
	return b.String()
}

// haltRoots are the configurations that stop on the next step.
// The single known cell is the symbol that transition reads.
func haltRoots(m Machine) []statNode {
	var roots []statNode
	for s := 0; s < m.N; s++ {
		for sym := 0; sym < 2; sym++ {
			tr := m.T[s][sym]
			if tr.Def && tr.Next >= 0 {
				continue
			}
			roots = append(roots, statNode{
				state: s,
				head:  0,
				lo:    0,
				hi:    0,
				tape:  statTape{0: byte(sym)},
			})
		}
	}
	return roots
}

func (n statNode) clone() statTape {
	t := make(statTape, len(n.tape)+1)
	for k, v := range n.tape {
		t[k] = v
	}
	return t
}

// predecessors undoes every transition that enters n.state.
func predecessors(m Machine, n statNode) []statNode {
	var out []statNode
	for s := 0; s < m.N; s++ {
		for sym := 0; sym < 2; sym++ {
			tr := m.T[s][sym]
			if !tr.Def || tr.Next != int8(n.state) {
				continue
			}
			prev := n.head - int(tr.Dir)
			if prev >= n.lo && prev <= n.hi {
				got, ok := n.tape[prev]
				if ok && got != tr.Write {
					continue
				}
				if !ok && tr.Write != 0 {
					continue
				}
			}
			tape := n.clone()
			tape[prev] = byte(sym)
			lo, hi := n.lo, n.hi
			if prev < lo {
				lo = prev
			}
			if prev > hi {
				hi = prev
			}
			out = append(out, statNode{
				state: s,
				head:  prev,
				lo:    lo,
				hi:    hi,
				depth: n.depth + 1,
				tape:  tape,
			})
		}
	}
	return out
}

// backwardClosed reports whether every reverse branch contradicts by depthLimit.
// The returned depth is the deepest consistent node. nodes is how many were expanded.
func backwardClosed(m Machine, roots []statNode, hist statHist, depthLimit, nodeCap int) (closed bool, depth, nodes int, rev statHist) {
	stack := append([]statNode(nil), roots...)
	for len(stack) > 0 {
		n := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		nodes++
		if nodes > nodeCap {
			return false, depth, nodes, rev
		}
		if n.depth > depth {
			depth = n.depth
		}
		if n.depth > depthLimit {
			return false, depth, nodes, rev
		}
		sym := byte(0)
		if v, ok := n.tape[n.head]; ok {
			sym = v
		}
		if n.state >= 0 && n.state < maxStates {
			rev.rev[n.state][sym]++
		}
		preds := predecessors(m, n)
		// Low forward counts are pushed first, so a frequent state/symbol is expanded next.
		for i := 1; i < len(preds); i++ {
			p := preds[i]
			w := hist.weight(p.state, int(p.tape[p.head]))
			j := i
			for j > 0 {
				q := preds[j-1]
				if hist.weight(q.state, int(q.tape[q.head])) <= w {
					break
				}
				preds[j] = q
				j--
			}
			preds[j] = p
		}
		stack = append(stack, preds...)
	}
	return true, depth, nodes, rev
}

// runForward counts each read and stops at halt or limit.
func runForward(m Machine, limit uint64) (Outcome, statHist) {
	var h statHist
	e := newEngine()
	e.load(m)
	e.limit = limit
	e.detect = false
	// A long run can visit millions of cells. The picture is only useful
	// for a short witness.
	e.wantTape = limit <= 4096
	e.reset()
	state := 0
	for e.steps < e.limit {
		i := e.ensure(e.head)
		e.touch(i)
		readPos := e.head
		e.markSpan(readPos)
		sym := e.c[i]
		if state >= 0 && state < maxStates {
			h.read[state][sym]++
		}
		if state < 0 || state >= e.n || !e.def[state][sym] {
			return e.finish(VerdictHalt, ReasonUndefined, state), h
		}
		tr := e.tr[state][sym]
		e.c[i] = tr.Write
		e.head += int(tr.Dir)
		e.steps++
		if tr.Next < 0 {
			e.ensure(e.head)
			return e.finish(VerdictHalt, ReasonHalt, -1), h
		}
		state = int(tr.Next)
	}
	e.ensure(e.head)
	return e.finish(VerdictUnknown, ReasonLimit, state), h
}

func applyStatMode(o Outcome, h statHist) Outcome {
	st, sym, n := h.mode()
	o.StatState = st
	o.StatSym = sym
	o.StatCount = n
	o.StatReads = h.total()
	o.StatLine = h.line()
	return o
}

// DecideStat searches forward from the blank tape and backward from every
// halting read. Halt is a forward witness. Loop is a closed backward tree
// whose depth the forward run has already passed. Anything else is unknown.
func DecideStat(m Machine, limit uint64) Outcome {
	if limit == 0 {
		limit = defaultLimit(m.N)
	}
	roots := haltRoots(m)
	if len(roots) == 0 {
		sample := limit
		if sample > 1024 {
			sample = 1024
		}
		o, h := runForward(m, sample)
		if o.Verdict == VerdictHalt {
			return applyStatMode(o, h)
		}
		o = applyStatMode(o, h)
		o.Verdict = VerdictLoop
		o.Reason = ReasonStat
		o.StatDepth = -1
		o.Start = o.Steps
		return o
	}
	o, h := runForward(m, limit)
	o = applyStatMode(o, h)
	if o.Verdict == VerdictHalt {
		return o
	}
	// A closed tree of depth H means a halting read is reached in at most H
	// steps. An explicit halt then occurs by step H+1; an undefined halt
	// occurs at step H, since that read does not count as a step. The
	// forward loop stops before inspecting the configuration at step
	// `limit`, so the tree may close only through limit-1. The run has
	// then already passed every halting read the tree still permits.
	depthLimit := int(limit) - 1
	if depthLimit > statMaxDepth {
		depthLimit = statMaxDepth
	}
	if depthLimit < 0 {
		depthLimit = 0
	}
	closed, depth, nodes, _ := backwardClosed(m, roots, h, depthLimit, statNodeCap)
	o.StatDepth = depth
	o.Period = uint64(nodes)
	o.Start = o.Steps
	if !closed || o.Steps < uint64(depth)+1 {
		o.Verdict = VerdictUnknown
		o.Reason = ReasonStat
		return o
	}
	o.Verdict = VerdictLoop
	o.Reason = ReasonStat
	return o
}
