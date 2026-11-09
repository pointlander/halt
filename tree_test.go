// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "testing"

func TestTreeRules(t *testing.T) {
	cases := []struct {
		src  string
		want string
		step int
	}{
		{"^", "^", 0},
		{"^ ^", "^ ^", 0},
		{"^ ^ ^", "^ ^ ^", 0},
		{"^ ^ ^ ^", "^", 1},
		{"^ (^ ^) ^ ^", "^ ^ (^ ^)", 1},
		{"^ (^ ^ ^) ^ ^", "^", 1},
		{"^ (^ ^ ^) ^ (^ ^)", "^ ^", 1},
		{"^ (^ ^ ^) ^ (^ ^ ^)", "^ ^ ^", 1},
		{"^ (^ ^ ^) ^ (^ ^ ^ ^)", "^", 2},
	}
	for _, c := range cases {
		term := mustTree(t, c.src)
		got := DecideTree(term, 100)
		if got.Verdict != VerdictHalt || got.Steps != c.step || got.Form != c.want {
			t.Fatalf("%s: %s form=%q steps=%d", c.src, got.Text(), got.Form, got.Steps)
		}
		if term.String() != c.src && c.step == 0 {
			t.Fatalf("print %s as %s", c.src, term)
		}
	}
}

func TestTreeNamedTerms(t *testing.T) {
	leaf := DecideTree(tApp(treeI(), tLeaf()), 1000)
	if leaf.Verdict != VerdictHalt || leaf.Form != "^" || leaf.Steps != 2 {
		t.Fatalf("I leaf: %s", leaf.Text())
	}
	iw := DecideTree(tApp(treeI(), treeOmega()), 1000)
	if iw.Verdict != VerdictHalt || iw.Form != treeOmega().String() || iw.Steps != 2 {
		t.Fatalf("I ω: %s", iw.Text())
	}
	nf := DecideTree(tApp(treeNot(), tLeaf()), 1000)
	if nf.Verdict != VerdictHalt || nf.Form != "^ ^" || nf.Steps != 1 {
		t.Fatalf("not false: %s", nf.Text())
	}
	nt := DecideTree(tApp(treeNot(), treeK()), 1000)
	if nt.Verdict != VerdictHalt || nt.Form != "^" || nt.Steps != 2 {
		t.Fatalf("not true: %s", nt.Text())
	}
	// The outer K discards ω ω. The copy inside the argument still loops.
	discard := DecideTree(tApp(tApp(treeK(), tLeaf()), tApp(treeOmega(), treeOmega())), 1000)
	if discard.Verdict != VerdictHalt || discard.Form != "^" || discard.Steps != 1 {
		t.Fatalf("K leaf (ω ω): %s", discard.Text())
	}
	// One developed term is enough: the block proof does not walk the graph.
	loop := DecideTree(tApp(treeOmega(), treeOmega()), 1)
	if loop.Verdict != VerdictLoop || loop.Note != treeBlockNote {
		t.Fatalf("ω ω: %s", loop.Text())
	}
}

func TestTreeCaps(t *testing.T) {
	// Developing the redex does not yet observe its value.
	early := DecideTree(mustTree(t, "^ ^ ^ ^"), 1)
	if early.Verdict != VerdictUnknown || early.Note != "step cap" {
		t.Fatalf("cap 1: %s", early.Text())
	}
	if _, err := ParseTree(""); err == nil {
		t.Fatal("empty term parsed")
	}
	if _, err := ParseTree("(^"); err == nil {
		t.Fatal("unclosed term parsed")
	}
	round, err := ParseTree(treeOmega().String())
	if err != nil || round.String() != treeOmega().String() {
		t.Fatalf("round trip %s -> %s %v", treeOmega(), round, err)
	}
	tri, err := ParseTree("△ (△ △) △")
	if err != nil || tri.String() != "^ (^ ^) ^" {
		t.Fatalf("triangle %s %v", tri, err)
	}
}

func TestTreeOmegaBlocks(t *testing.T) {
	w := treeOmega()
	start := tApp(w, w)
	cur := start
	for i := 0; i < 3; i++ {
		next, ok := cur.parReduct()
		if !ok {
			t.Fatalf("value at parallel step %d", i)
		}
		cur = next
	}
	if !treeEq(cur, start) {
		t.Fatalf("parallel outermost period: %s", cur)
	}

	// △ (△ ^ ^) (ω ω) (^ ^ ^ ^) has a value by rule 3a once the last
	// argument is reduced. The leftmost subterm is the looping one.
	fork := tApp(tApp(tLeaf(), tApp(tApp(tLeaf(), tLeaf()), tLeaf())), start)
	term := tApp(fork, mustTree(t, "^ ^ ^ ^"))
	got := DecideTree(term, 20)
	if got.Verdict != VerdictHalt || got.Form != "^" || got.Steps != 2 {
		t.Fatalf("discarded loop: %s", got.Text())
	}

	// △ (△ K) △ is an identity, but it is not the book's I, so the ω-block
	// proof does not apply. Parallel outermost still repeats after 3 steps.
	k := treeK()
	j := tApp(tApp(tLeaf(), tApp(tLeaf(), k)), tLeaf())
	wj := tApp(tApp(tLeaf(), tApp(tLeaf(), j)), j)
	small := DecideTree(tApp(wj, wj), 30)
	if small.Verdict != VerdictLoop || small.Steps != 3 || small.Note == treeBlockNote {
		t.Fatalf("small identity self-application: %s", small.Text())
	}

	seen := map[string]struct{}{}
	q := []*treeTerm{start}
	for len(q) > 0 && len(seen) < 200 {
		cur := q[0]
		q = q[1:]
		k, ok := cur.key(treeByteCap)
		if !ok {
			t.Fatal("size cap during closure check")
		}
		if _, ok := seen[k]; ok {
			continue
		}
		seen[k] = struct{}{}
		if !proveOmega(cur) {
			t.Fatalf("left the block grammar: %s", k)
		}
		rs := cur.reducts()
		if len(rs) == 0 {
			t.Fatalf("value in the block grammar: %s", k)
		}
		q = append(q, rs...)
	}
	if len(seen) < 20 {
		t.Fatalf("closure sample %d", len(seen))
	}
}

func mustTree(t *testing.T, src string) *treeTerm {
	t.Helper()
	term, err := ParseTree(src)
	if err != nil {
		t.Fatal(err)
	}
	return term
}
