// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"strings"
	"unicode"
	"unicode/utf8"
)

// Triage-calculus terms, the five-rule tree calculus.
//
// A term is a leaf or an application. Application is left-associative.
// Writing △ for the leaf, the rules are:
//
//	△ △ y z           ⟶  y
//	△ (△ x) y z       ⟶  x z (y z)
//	△ (△ w x) y △     ⟶  w
//	△ (△ w x) y (△ u) ⟶  x u
//	△ (△ w x) y (△ u v) ⟶  y u v
//
// A term halts when a reduction reaches a value: a tree of leaves,
// stems, and forks, with no subterm of the form △ a b c. The search
// contracts every outermost redex in one step. The rules are
// left-linear and non-overlapping, so this parallel-outermost strategy
// reaches a value whenever one exists. A repeated term on that path is
// a loop. So is an application of two ω-blocks, by the closure argument
// on isBlock: that proof does not wait for the cycle. A copy of ω ω
// discarded by rule 1 is not a loop. A search that hits the step cap or
// the printed-size cap is unknown. No term decides halting for every term.

const (
	treeStepCap    = 10_000
	treeStepCapMax = 100_000
	treeByteCap    = 4_096
	treeDepthCap   = 10_000
)

// treeTerm is an immutable application tree. The zero value is not a term;
// a leaf is a non-nil pointer with app false.
type treeTerm struct {
	app bool
	fun *treeTerm
	arg *treeTerm
}

func tLeaf() *treeTerm { return &treeTerm{} }

func tApp(fun, arg *treeTerm) *treeTerm {
	return &treeTerm{app: true, fun: fun, arg: arg}
}

// treeK is △ △, which is also the boolean true.
func treeK() *treeTerm { return tApp(tLeaf(), tLeaf()) }

// treeI is △ (△ (△ △)) (△ △), the combinator I = S K K.
func treeI() *treeTerm {
	k := treeK()
	return tApp(tApp(tLeaf(), tApp(tLeaf(), k)), k)
}

// treeNot is △ (△ (△ △) (△ △ △)) △.
func treeNot() *treeTerm {
	k := treeK()
	y := tApp(tApp(tLeaf(), k), tApp(k, tLeaf()))
	return tApp(tApp(tLeaf(), y), tLeaf())
}

// treeOmega is △ (△ I) I.
func treeOmega() *treeTerm {
	i := treeI()
	return tApp(tApp(tLeaf(), tApp(tLeaf(), i)), i)
}

// write appends the fully parenthesized left-associative spelling.
// ok is false when the unfolded text or the nesting would pass the cap.
func (t *treeTerm) write(b *strings.Builder, budget, depth int) bool {
	if t == nil || depth > treeDepthCap || b.Len() > budget {
		return false
	}
	if !t.app {
		b.WriteByte('^')
		return b.Len() <= budget
	}
	if !t.fun.write(b, budget, depth+1) {
		return false
	}
	b.WriteByte(' ')
	if t.arg.app {
		b.WriteByte('(')
		if !t.arg.write(b, budget, depth+1) {
			return false
		}
		b.WriteByte(')')
		return b.Len() <= budget
	}
	return t.arg.write(b, budget, depth+1)
}

func (t *treeTerm) String() string {
	s, ok := t.key(treeByteCap)
	if !ok {
		return ""
	}
	return s
}

func (t *treeTerm) key(budget int) (string, bool) {
	var b strings.Builder
	if !t.write(&b, budget, 0) {
		return "", false
	}
	return b.String(), true
}

// contract reduces a root redex. Subterms are not reduced.
func (t *treeTerm) contract() (*treeTerm, bool) {
	if t == nil || !t.app || t.fun == nil || !t.fun.app || t.fun.fun == nil || !t.fun.fun.app {
		return nil, false
	}
	// t = ((△ a) y) z
	z := t.arg
	y := t.fun.arg
	op := t.fun.fun
	if op.fun == nil || op.fun.app || op.arg == nil {
		return nil, false
	}
	a := op.arg
	if !a.app {
		// △ △ y z ⟶ y
		return y, true
	}
	if a.fun != nil && !a.fun.app {
		// △ (△ x) y z ⟶ x z (y z)
		x := a.arg
		return tApp(tApp(x, z), tApp(y, z)), true
	}
	if a.fun == nil || a.fun.fun == nil || a.fun.fun.app {
		return nil, false
	}
	// a = △ w x
	w := a.fun.arg
	x := a.arg
	if z != nil && !z.app {
		// △ (△ w x) y △ ⟶ w
		return w, true
	}
	if z != nil && z.app && z.fun != nil && !z.fun.app {
		// △ (△ w x) y (△ u) ⟶ x u
		return tApp(x, z.arg), true
	}
	if z != nil && z.app && z.fun != nil && z.fun.app && z.fun.fun != nil && !z.fun.fun.app {
		// △ (△ w x) y (△ u v) ⟶ y u v
		return tApp(tApp(y, z.fun.arg), z.arg), true
	}
	return nil, false
}

// parReduct contracts every outermost redex. The root redex, when there
// is one, is the only outermost redex. Otherwise the outermost redexes
// lie in the two children and are contracted together.
func (t *treeTerm) parReduct() (*treeTerm, bool) {
	if t == nil {
		return nil, false
	}
	if r, ok := t.contract(); ok {
		return r, true
	}
	if !t.app {
		return nil, false
	}
	fun, fok := t.fun.parReduct()
	arg, aok := t.arg.parReduct()
	if !fok && !aok {
		return nil, false
	}
	if !fok {
		fun = t.fun
	}
	if !aok {
		arg = t.arg
	}
	return tApp(fun, arg), true
}

// reducts is every one-step contraction, root first, then left, then right.
func (t *treeTerm) reducts() []*treeTerm {
	if t == nil {
		return nil
	}
	var out []*treeTerm
	if r, ok := t.contract(); ok {
		out = append(out, r)
	}
	if !t.app {
		return out
	}
	for _, f := range t.fun.reducts() {
		out = append(out, tApp(f, t.arg))
	}
	for _, a := range t.arg.reducts() {
		out = append(out, tApp(t.fun, a))
	}
	return out
}

// TreeResult is a witnessed tree-calculus decision.
type TreeResult struct {
	Verdict Verdict
	Steps   int
	Nodes   int
	Form    string
	Note    string
}

func (r TreeResult) Text() string {
	switch r.Verdict {
	case VerdictHalt:
		return fmt.Sprintf("halts at step %s as %s", comma(uint64(r.Steps)), r.Form)
	case VerdictLoop:
		why := r.Note
		if why == "" {
			why = "reduction repeats"
		}
		return "does not halt: " + why
	default:
		why := r.Note
		if why == "" {
			why = "step cap"
		}
		return fmt.Sprintf("unknown: tree search hit the %s (%s %s)", why, comma(uint64(r.Steps)), stepsWord(uint64(r.Steps)))
	}
}

const treeBlockNote = "an application of two ω-blocks, and every reduct is again such an application"

// DecideTree searches by parallel outermost reduction.
// stepCap bounds how many terms of that path are developed, including
// the start. A non-positive cap selects the default.
func DecideTree(t *treeTerm, stepCap int) TreeResult {
	if t == nil {
		return TreeResult{Verdict: VerdictUnknown, Note: "empty term"}
	}
	if stepCap <= 0 {
		stepCap = treeStepCap
	}
	if stepCap > treeStepCapMax {
		stepCap = treeStepCapMax
	}
	if proveOmega(t) {
		return TreeResult{Verdict: VerdictLoop, Note: treeBlockNote}
	}
	seen := map[string]int{}
	cur := t
	for step := 0; step < stepCap; step++ {
		k, ok := cur.key(treeByteCap)
		if !ok {
			if proveOmega(cur) {
				return TreeResult{Verdict: VerdictLoop, Steps: step, Note: treeBlockNote}
			}
			return TreeResult{Verdict: VerdictUnknown, Steps: step, Note: "size cap"}
		}
		if prev, ok := seen[k]; ok {
			return TreeResult{
				Verdict: VerdictLoop,
				Steps:   step - prev,
				Note:    fmt.Sprintf("parallel outermost reduction repeats a term, period %s", comma(uint64(step-prev))),
			}
		}
		seen[k] = step
		next, ok := cur.parReduct()
		if !ok {
			return TreeResult{Verdict: VerdictHalt, Steps: step, Nodes: len(seen), Form: k}
		}
		if proveOmega(next) {
			return TreeResult{Verdict: VerdictLoop, Steps: step + 1, Note: treeBlockNote}
		}
		cur = next
	}
	if proveOmega(cur) {
		return TreeResult{Verdict: VerdictLoop, Steps: stepCap, Note: treeBlockNote}
	}
	return TreeResult{Verdict: VerdictUnknown, Steps: stepCap, Note: "step cap"}
}

// proveOmega reports whether t is an application of two ω-blocks.
//
// K is △ △, I is △ (△ K) K, and ω is △ (△ I) I. A block is ω, or I
// applied to a block, or (K b1) (K b2) for blocks b1 and b2. The only
// block in normal form is ω: I b is a rule-2 redex and (K b1) (K b2)
// is a rule-1 redex, and each of those reducts is a block again.
//
// If b1 and b2 are blocks, b1 b2 always has a redex. When b1 is not ω
// the redex is inside b1 and the root is not a redex, so every one-step
// reduct is b1' b2 or b1 b2' with both sides still blocks. When b1 is ω
// the root is rule 2, with reduct (I b2) (I b2); an inner step replaces
// b2 by another block. No such application has a normal form. Rule 1
// can still discard one, which is why K leaf (ω ω) halts.
func proveOmega(t *treeTerm) bool {
	if t == nil || !t.app {
		return false
	}
	w := treeOmega()
	i := treeI()
	k := treeK()
	if !isBlock(t.fun, w, i, k, 0) || !isBlock(t.arg, w, i, k, 0) {
		return false
	}
	if _, ok := t.parReduct(); !ok {
		return false
	}
	return true
}

func isBlock(t, w, i, k *treeTerm, depth int) bool {
	if t == nil || depth > treeDepthCap {
		return false
	}
	if treeEq(t, w) {
		return true
	}
	if t.app && treeEq(t.fun, i) && isBlock(t.arg, w, i, k, depth+1) {
		return true
	}
	// (K b1) (K b2)
	if t.app && t.fun != nil && t.fun.app && treeEq(t.fun.fun, k) &&
		t.arg != nil && t.arg.app && treeEq(t.arg.fun, k) &&
		isBlock(t.fun.arg, w, i, k, depth+1) && isBlock(t.arg.arg, w, i, k, depth+1) {
		return true
	}
	return false
}

func treeEq(a, b *treeTerm) bool {
	if a == nil || b == nil {
		return a == b
	}
	if a.app != b.app {
		return false
	}
	if !a.app {
		return true
	}
	return treeEq(a.fun, b.fun) && treeEq(a.arg, b.arg)
}

// ParseTree reads a term. ^, △, and Δ are the leaf. Application is
// juxtaposition and associates to the left. Parentheses group.
func ParseTree(src string) (*treeTerm, error) {
	p := treeParser{s: src}
	t, err := p.parseTerm()
	if err != nil {
		return nil, err
	}
	p.skip()
	if p.i < len(p.s) {
		return nil, fmt.Errorf("trailing input at %d", p.i)
	}
	if t == nil {
		return nil, fmt.Errorf("empty tree term")
	}
	return t, nil
}

type treeParser struct {
	s string
	i int
}

func (p *treeParser) skip() {
	for p.i < len(p.s) {
		r, n := utf8.DecodeRuneInString(p.s[p.i:])
		if !unicode.IsSpace(r) {
			return
		}
		p.i += n
	}
}

func (p *treeParser) parseTerm() (*treeTerm, error) {
	p.skip()
	left, err := p.parseAtom()
	if err != nil {
		return nil, err
	}
	for {
		p.skip()
		if p.i >= len(p.s) {
			return left, nil
		}
		r, _ := utf8.DecodeRuneInString(p.s[p.i:])
		if r == ')' {
			return left, nil
		}
		right, err := p.parseAtom()
		if err != nil {
			return nil, err
		}
		left = tApp(left, right)
	}
}

func (p *treeParser) parseAtom() (*treeTerm, error) {
	p.skip()
	if p.i >= len(p.s) {
		return nil, fmt.Errorf("empty tree term")
	}
	r, n := utf8.DecodeRuneInString(p.s[p.i:])
	switch r {
	case '^', '△', 'Δ':
		p.i += n
		return tLeaf(), nil
	case '(':
		p.i += n
		t, err := p.parseTerm()
		if err != nil {
			return nil, err
		}
		p.skip()
		if p.i >= len(p.s) || p.s[p.i] != ')' {
			return nil, fmt.Errorf("unclosed parenthesis at %d", p.i)
		}
		p.i++
		return t, nil
	default:
		return nil, fmt.Errorf("bad tree term at %d", p.i)
	}
}
