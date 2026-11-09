// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

// A 2-state blank-tape machine as a triage term.
//
// DecideTree is the proof. The Go code only compiles the transition table.
// A halt value is the unary triple (steps, ones, space): zero is a leaf and
// the successor of n is the stem of n. A loop is an application of two
// ω-blocks, or a repeated term. Reaching an undefined read is a different
// value, cons(state, symbol), so the enumerator can fill that read. It is
// not a halt score: an undefined read writes nothing and does not count a
// step, and tree-normal-form search fills it instead of scoring it.
//
// Nothing here treats a published S(2), Σ(2), or space(2) as a bound.

func triage(w, x, y *treeTerm) *treeTerm {
	return tApp(tApp(tLeaf(), tApp(tApp(tLeaf(), w), x)), y)
}

func bit1() *treeTerm { return treeK() }

// onPair(k) applied to cons(a, b) reduces to (k a) b.
func onPair(k *treeTerm) *treeTerm { return triage(tLeaf(), tLeaf(), k) }

// onBit(no, yes) applied to a bit selects no (leaf) or yes (△ △).
func onBit(no, yes *treeTerm) *treeTerm {
	return triage(no, tApp(treeK(), yes), tLeaf())
}

// waitVal(m, n) is a value. Applied to p it reduces to m n (I p), and I p
// reduces to p. The application is the redex, so m and n are not copied
// while some other argument is still running.
func waitVal(m, n *treeTerm) *treeTerm {
	return s2(s2(k1(m), k1(n)), treeI())
}

// zFix is a fixpoint that stays a value until it is applied. Θ f unfolds
// on every parallel step, and each unfold copies f. Z f waits as a value,
// and Z f x reduces to f (Z f) x.
func zFix(f *treeTerm) *treeTerm {
	w := 0
	bz := compileLam(lamAbs(w, waitApply(treeOmega(), lvar(w))))
	return waitVal(treeOmega(), s2(k1(f), bz))
}

func waitApply(m *treeTerm, n *lam) *lam {
	km := lval(k1(m))
	kn := lapp(lval(treeK()), n)
	inner := lapp(lapp(lval(tLeaf()), lapp(lval(tLeaf()), km)), kn)
	return lapp(lapp(lval(tLeaf()), lapp(lval(tLeaf()), inner)), lval(treeI()))
}

func cons(h, tl *treeTerm) *treeTerm { return tApp(tApp(tLeaf(), h), tl) }

func unary(n int) *treeTerm {
	t := tLeaf()
	for i := 0; i < n; i++ {
		t = tApp(tLeaf(), t)
	}
	return t
}

func bitOf(b byte) *treeTerm {
	if b == 0 {
		return tLeaf()
	}
	return bit1()
}

// s2 is the value △ (△ u) v. Applied to z it reduces to u z (v z).
func s2(u, v *treeTerm) *treeTerm {
	return tApp(tApp(tLeaf(), tApp(tLeaf(), u)), v)
}

// k1 is K x, the value △ △ x.
func k1(x *treeTerm) *treeTerm { return tApp(treeK(), x) }

// transTerm encodes one transition.
//
//	leaf                 undefined (the enumerator fills this read)
//	stem(write)          explicit halt
//	fork(write, fork(dir, next))  a step
//
// A leaf is 0, left, or state A. △ △ is 1, right, or state B.
func transTerm(t Trans) *treeTerm {
	if !t.Def {
		return tLeaf()
	}
	w := bitOf(t.Write)
	if t.Next < 0 {
		return tApp(tLeaf(), w)
	}
	dir := tLeaf()
	if t.Dir > 0 {
		dir = bit1()
	}
	next := tLeaf()
	if t.Next > 0 {
		next = bit1()
	}
	return cons(w, cons(dir, next))
}

// predFn n reduces to n-1, and predFn 0 reduces to 0.
func predFn() *treeTerm { return triage(tLeaf(), treeI(), tLeaf()) }

type lamGen struct{ n int }

func (g *lamGen) id() int {
	g.n++
	return g.n
}

func lcons(h, tl *lam) *lam { return lapp(lapp(lval(tLeaf()), h), tl) }

func lstem(x *lam) *lam { return lapp(lval(tLeaf()), x) }

func ltriage(w, x, y *lam) *lam {
	return lapp(lapp(lval(tLeaf()), lapp(lapp(lval(tLeaf()), w), x)), y)
}

// lams binds ids from the outside in: the first id is the first argument.
func lams(ids []int, body *lam) *lam {
	for i := len(ids) - 1; i >= 0; i-- {
		body = lamAbs(ids[i], body)
	}
	return body
}

// shape cases on a value. A leaf returns onLeaf. A stem applies onStem to
// the payload. A fork applies onFork to the two fields.
func (g *lamGen) shape(v *lam, onLeaf *lam, onStem func(*lam) *lam, onFork func(*lam, *lam) *lam) *lam {
	u := g.id()
	a, b := g.id(), g.id()
	stemB := lamAbs(u, onStem(lvar(u)))
	forkB := lamAbs(a, lamAbs(b, onFork(lvar(a), lvar(b))))
	return lapp(ltriage(onLeaf, stemB, forkB), v)
}

// ifBit selects a branch. Zero is a leaf and one is △ △.
func ifBit(b, no, yes *lam) *lam {
	return lapp(ltriage(no, lapp(lval(treeK()), yes), lval(tLeaf())), b)
}

func (g *lamGen) uncons(v *lam, k func(*lam, *lam) *lam) *lam {
	a, b := g.id(), g.id()
	fn := lamAbs(a, lamAbs(b, k(lvar(a), lvar(b))))
	return lapp(ltriage(lval(tLeaf()), lval(tLeaf()), fn), v)
}

// --- one step ---------------------------------------------------------------
//
// The config is
//
//	cons(state, cons(sym, cons(rightRest, cons(left, cons(steps, cons(ones, space))))))
//
// rightRest is the right list without the current cell. left is the cells
// strictly left of the head, nearest first. The current cell is sym.
//
// Each tape variable occurs once. A case that needs the variable returns a
// function, and the variable is applied outside the case, so bracket
// abstraction wraps the other arm instead of copying it.

// succAsFn is the successor function. λn. △ n is the leaf, by eta.
func succAsFn() *treeTerm { return tLeaf() }

// haltFn is λns λno λnp. cons(cons(ns, cons(no, np)), leaf).
// The fixpoint's K keeps the score triple and discards the leaf.
func haltFn() *treeTerm {
	g := &lamGen{}
	ns, no, np := g.id(), g.id(), g.id()
	scores := lcons(lvar(ns), lcons(lvar(no), lvar(np)))
	body := lcons(scores, lval(tLeaf()))
	return compileLam(lams([]int{ns, no, np}, body))
}

// contFn is λtape λns λno λnp. stem(config).
// tape is cons(state, cons(sym, cons(rightRest, left))).
func contFn() *treeTerm {
	g := &lamGen{}
	tape, ns, no, np := g.id(), g.id(), g.id(), g.id()
	body := g.uncons(lvar(tape), func(st, r1 *lam) *lam {
		return g.uncons(r1, func(sy, r2 *lam) *lam {
			return g.uncons(r2, func(rr, left *lam) *lam {
				cfg := lcons(st, lcons(sy, lcons(rr, lcons(left, lcons(lvar(ns), lcons(lvar(no), lvar(np)))))))
				return lstem(cfg)
			})
		})
	})
	return compileLam(lams([]int{tape, ns, no, np}, body))
}

// needFn is λst λsy. cons(cons(st, sy), leaf). K keeps cons(state, symbol).
func needFn() *treeTerm {
	g := &lamGen{}
	st, sy := g.id(), g.id()
	body := lcons(lcons(lvar(st), lvar(sy)), lval(tLeaf()))
	return compileLam(lams([]int{st, sy}, body))
}

func (g *lamGen) finish(steps, ones, space, plan *lam) *lam {
	return g.uncons(plan, func(stepsOp, r1 *lam) *lam {
		return g.uncons(r1, func(onesOp, r2 *lam) *lam {
			return g.uncons(r2, func(spaceOp, tag *lam) *lam {
				ns := lapp(stepsOp, steps)
				no := lapp(onesOp, ones)
				np := lapp(spaceOp, space)
				return g.applyTag(tag, ns, no, np)
			})
		})
	})
}

// applyTag applies the 3-argument continuation carried by tag to the
// three counters. Each counter occurs once, as an argument.
func (g *lamGen) applyTag(tag, ns, no, np *lam) *lam {
	halt := lval(haltFn())
	cont := lval(contFn())
	sel := g.shape(tag,
		halt,
		func(tape *lam) *lam { return lapp(cont, tape) },
		func(_, _ *lam) *lam { return halt },
	)
	return lapp(lapp(lapp(sel, ns), no), np)
}

// onesOp is the function applied to the ones counter.
// 0→1 increments, 1→0 decrements, and writing the symbol already there
// leaves the counter alone.
func (g *lamGen) onesOp(sym, write *lam) *lam {
	id := lval(treeI())
	up := lval(succAsFn())
	down := lval(predFn())
	return ifBit(sym, ifBit(write, id, up), ifBit(write, down, id))
}

func lHaltPlan(stepsOp, onesOp, spaceOp *lam) *lam {
	return lcons(stepsOp, lcons(onesOp, lcons(spaceOp, lval(tLeaf()))))
}

// edgeInfo cases on a side list once.
// An empty list becomes (successor, 0, nil): the fresh cell is blank and
// space grows. A cons becomes (identity, head, tail).
func (g *lamGen) edgeInfo(list *lam) *lam {
	blank := lcons(lval(succAsFn()), lcons(lval(tLeaf()), lval(tLeaf())))
	return g.shape(list,
		blank,
		func(*lam) *lam { return blank },
		func(h, tl *lam) *lam { return lcons(lval(treeI()), lcons(h, tl)) },
	)
}

// sideFn(rr, left, write, next) returns cons(spaceOp, tape).
// dir chooses the side. leaf is left, △ △ is right.
func sideFn(dir, rr, left, write, next *lam) *lam {
	picked := ifBit(dir, lval(leftStep()), lval(rightStep()))
	return lapp(lapp(lapp(lapp(picked, rr), left), write), next)
}

func rightStep() *treeTerm {
	g := &lamGen{}
	rr, left, write, next := g.id(), g.id(), g.id(), g.id()
	body := g.uncons(g.edgeInfo(lvar(rr)), func(spaceOp, rest *lam) *lam {
		return g.uncons(rest, func(sym, newRR *lam) *lam {
			newLeft := lcons(lvar(write), lvar(left))
			tape := lcons(lvar(next), lcons(sym, lcons(newRR, newLeft)))
			return lcons(spaceOp, tape)
		})
	})
	return compileLam(lams([]int{rr, left, write, next}, body))
}

func leftStep() *treeTerm {
	g := &lamGen{}
	rr, left, write, next := g.id(), g.id(), g.id(), g.id()
	body := g.uncons(g.edgeInfo(lvar(left)), func(spaceOp, rest *lam) *lam {
		return g.uncons(rest, func(sym, newLeft *lam) *lam {
			newRR := lcons(lvar(write), lvar(rr))
			tape := lcons(lvar(next), lcons(sym, lcons(newRR, newLeft)))
			return lcons(spaceOp, tape)
		})
	})
	return compileLam(lams([]int{rr, left, write, next}, body))
}

func transSlot(m Machine, st, sy int) *treeTerm {
	if m.N <= st {
		return tLeaf()
	}
	return transTerm(m.T[st][sy])
}

// ofCounters builds λsteps λones λspace. body, with those three bound.
func (g *lamGen) ofCounters(body func(steps, ones, space *lam) *lam) *lam {
	s, o, p := g.id(), g.id(), g.id()
	return lams([]int{s, o, p}, body(lvar(s), lvar(o), lvar(p)))
}

// step7 is λstate λsym λright λleft λsteps λones λspace. answer.
// The case on the transition returns a function of the three counters,
// and the counters are applied once, outside the case.
func step7(m Machine) *lam {
	g := &lamGen{}
	st, sy, rr, left := g.id(), g.id(), g.id(), g.id()
	steps, ones, space := g.id(), g.id(), g.id()
	body := g.stepBody(m, lvar(st), lvar(sy), lvar(rr), lvar(left), lvar(steps), lvar(ones), lvar(space))
	return lams([]int{st, sy, rr, left, steps, ones, space}, body)
}

func (g *lamGen) stepBody(m Machine, st, sy, rr, left, steps, ones, space *lam) *lam {
	tr := ifBit(st,
		ifBit(sy, lval(transSlot(m, 0, 0)), lval(transSlot(m, 0, 1))),
		ifBit(sy, lval(transSlot(m, 1, 0)), lval(transSlot(m, 1, 1))),
	)
	fn := g.shape(tr,
		g.needArm(st, sy),
		func(write *lam) *lam { return g.haltArm(lval(succAsFn()), g.onesOp(sy, write), lval(treeI())) },
		func(write, rest *lam) *lam {
			return g.shape(rest,
				g.haltArm(lval(treeI()), lval(treeI()), lval(treeI())),
				func(*lam) *lam { return g.haltArm(lval(treeI()), lval(treeI()), lval(treeI())) },
				func(dir, next *lam) *lam { return g.moveArm(write, dir, next, sy, rr, left) },
			)
		},
	)
	return lapp(lapp(lapp(fn, steps), ones), space)
}

// needArm ignores the counters and returns cons(cons(state, symbol), leaf).
func (g *lamGen) needArm(st, sy *lam) *lam {
	return g.ofCounters(func(_, _, _ *lam) *lam {
		return lapp(lapp(lval(needFn()), st), sy)
	})
}

// haltArm returns cons(cons(steps, cons(ones, space)), leaf).
// An explicit halt passes the successor and the ones adjustment.
// The cell moved onto is not read, so space is the identity.
func (g *lamGen) haltArm(stepsOp, onesOp, spaceOp *lam) *lam {
	return g.ofCounters(func(steps, ones, space *lam) *lam {
		ns := lapp(stepsOp, steps)
		no := lapp(onesOp, ones)
		np := lapp(spaceOp, space)
		return lapp(lapp(lapp(lval(haltFn()), ns), no), np)
	})
}

// moveArm returns the stem of the next config.
func (g *lamGen) moveArm(write, dir, next, sy, rr, left *lam) *lam {
	return g.ofCounters(func(steps, ones, space *lam) *lam {
		fields := sideFn(dir, rr, left, write, next)
		onesOp := g.onesOp(sy, write)
		return g.uncons(fields, func(spaceOp, tape *lam) *lam {
			ns := lapp(lval(succAsFn()), steps)
			no := lapp(onesOp, ones)
			np := lapp(spaceOp, space)
			return lapp(lapp(lapp(lapp(lval(contFn()), tape), ns), no), np)
		})
	})
}

// unpack7 k cfg peels a config and applies k to its seven fields.
// k is used once, so the step function is not copied into every branch.
func unpack7() *lam {
	g := &lamGen{}
	k, cfg := g.id(), g.id()
	peeled := g.uncons(lvar(cfg), func(st, r1 *lam) *lam {
		return g.uncons(r1, func(sy, r2 *lam) *lam {
			return g.uncons(r2, func(rr, r3 *lam) *lam {
				return g.uncons(r3, func(left, r4 *lam) *lam {
					return g.uncons(r4, func(steps, r5 *lam) *lam {
						return g.uncons(r5, func(ones, space *lam) *lam {
							return lapp(lapp(lapp(lapp(lapp(lapp(lapp(lvar(k), st), sy), rr), left), steps), ones), space)
						})
					})
				})
			})
		})
	})
	return lams([]int{k, cfg}, peeled)
}

// stepTerm compiles the one-step function.
func stepTerm(m Machine) *treeTerm {
	return tApp(compileLam(unpack7()), compileLam(step7(m)))
}

// initialCfg is state A on a blank tape. The current cell is an explicit
// zero, so the right rest and the left list are empty. Space is 1 because
// that cell is read.
func initialCfg() *treeTerm {
	z := tLeaf()
	return cons(z, cons(z, cons(z, cons(z, cons(z, cons(z, unary(1)))))))
}

// machineTerm is the fixpoint of the step on a blank tape.
// The step result is a leaf (reserved for a loop proof), a stem of the
// next config, or a fork. K on a fork returns the payload: a score triple
// or the undefined read cons(state, symbol).
func machineTerm(m Machine) *treeTerm {
	self, cfg := 0, 1
	ww := tApp(treeOmega(), treeOmega())
	body := lapp(ltriage(lval(ww), lvar(self), lval(treeK())), lapp(lval(stepTerm(m)), lvar(cfg)))
	f := compileLam(lams([]int{self, cfg}, body))
	return tApp(turingFix(f), initialCfg())
}

func asFork(t *treeTerm) (a, b *treeTerm, ok bool) {
	if t == nil || !t.app || t.fun == nil || !t.fun.app || t.fun.fun == nil || t.fun.fun.app {
		return nil, nil, false
	}
	return t.fun.arg, t.arg, true
}

func asStem(t *treeTerm) (a *treeTerm, ok bool) {
	if t == nil || !t.app || t.fun == nil || t.fun.app {
		return nil, false
	}
	return t.arg, true
}

func asUnary(t *treeTerm) (int, bool) {
	n := 0
	for {
		if t == nil {
			return 0, false
		}
		if !t.app {
			return n, true
		}
		a, ok := asStem(t)
		if !ok {
			return 0, false
		}
		t = a
		n++
		if n > 100000 {
			return 0, false
		}
	}
}

// scoresOf reads a halt value cons(steps, cons(ones, space)).
func scoresOf(t *treeTerm) (steps, ones, space int, ok bool) {
	stepsT, rest, ok := asFork(t)
	if !ok {
		return 0, 0, 0, false
	}
	onesT, spaceT, ok := asFork(rest)
	if !ok {
		return 0, 0, 0, false
	}
	steps, ok1 := asUnary(stepsT)
	ones, ok2 := asUnary(onesT)
	space, ok3 := asUnary(spaceT)
	if !ok1 || !ok2 || !ok3 {
		return 0, 0, 0, false
	}
	return steps, ones, space, true
}

// needOf reads the undefined-read value cons(state, symbol).
// A score triple has a fork as its second field, so the two values
// are not confused.
func needOf(t *treeTerm) (state, sym int, ok bool) {
	a, b, fork := asFork(t)
	if !fork {
		return 0, 0, false
	}
	if _, _, inner := asFork(b); inner {
		return 0, 0, false
	}
	st, ok1 := asBit(a)
	sy, ok2 := asBit(b)
	if !ok1 || !ok2 {
		return 0, 0, false
	}
	return st, sy, true
}

func asBit(t *treeTerm) (int, bool) {
	if t == nil {
		return 0, false
	}
	if !t.app {
		return 0, true
	}
	if t.fun != nil && !t.fun.app && t.arg != nil && !t.arg.app {
		return 1, true
	}
	return 0, false
}
