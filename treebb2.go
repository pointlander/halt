// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"os"
)

// BB2 is decided by one triage term per machine. The term holds the
// transition table and a blank-tape simulator. Parallel outermost
// reduction is the proof: a score value is a halt, and a loop is either
// ω ω or a repeated term. The closed-graph case reduces to ω ω by the
// triage rules and discards the simulator. A step cap or the byte cap is
// unknown, never a loop.

const bbByteCap = 1024 * 1024 * 1024

// BB2Result is the busy-beaver scoreboard proved by tree reduction.
// Proved is false when any machine is unknown. The three scores are then
// only lower bounds from the machines that did halt.
type BB2Result struct {
	Proved  bool
	Nodes   int
	Halted  int
	Looping int
	Unknown int

	Steps BB2Score
	Ones  BB2Score
	Space BB2Score

	Open []string
	// Done is every machine the tree settled, in search order.
	Done []BB2Done
}

// BB2Score is one extreme halting machine.
type BB2Score struct {
	Spec  string
	Steps uint64
	Ones  int
	Space int
}

// BB2Done is one settled machine.
type BB2Done struct {
	Spec    string
	Verdict Verdict
	Steps   int
	Ones    int
	Space   int
}

func (r BB2Result) Text() string {
	if !r.Proved {
		return fmt.Sprintf("BB2 is not proved (%d unknown, %d halted, %d looping)", r.Unknown, r.Halted, r.Looping)
	}
	return fmt.Sprintf("S(2) = %d (%s), Σ(2) = %d (%s), space(2) = %d (%s)",
		r.Steps.Steps, r.Steps.Spec, r.Ones.Ones, r.Ones.Spec, r.Space.Space, r.Space.Spec)
}

// SolveBB2 decides every 2-state tree-normal-form machine by reduction.
// The walk is the TNF enumeration. It does not call Search, Decide, or the
// simulator: an undefined read is whatever value the term returns.
func SolveBB2() BB2Result {
	var res BB2Result
	var tr [2][2]Trans
	tr[0][0] = Trans{Write: 1, Dir: 1, Next: 1, Def: true}
	cand := transitionChoices(2, 2)
	var walk func()
	walk = func() {
		res.Nodes++
		m := Machine{N: 2, T: [][2]Trans{tr[0], tr[1]}}
		spec := m.String()
		r := DecideTreeLimit(bb2Term(m), treeStepCapMax, bbByteCap)
		switch r.Verdict {
		case VerdictLoop:
			res.Looping++
			res.Done = append(res.Done, BB2Done{Spec: spec, Verdict: VerdictLoop})
			fmt.Fprintf(os.Stderr, "  loop %s\n", spec)
		case VerdictHalt:
			if st, sy, ok := treeNeed(r.Form); ok {
				if st < 0 || st > 1 || sy < 0 || sy > 1 {
					res.Unknown++
					res.noteOpen(spec)
					fmt.Fprintf(os.Stderr, "  unknown %s (bad need)\n", spec)
					return
				}
				for _, c := range cand {
					tr[st][sy] = c
					walk()
					tr[st][sy] = Trans{}
				}
				return
			}
			steps, ones, space, ok := treeScore(r.Form)
			if !ok {
				res.Unknown++
				res.noteOpen(spec)
				fmt.Fprintf(os.Stderr, "  unknown %s (halt value)\n", spec)
				return
			}
			res.Halted++
			res.noteHalt(spec, steps, ones, space)
			res.Done = append(res.Done, BB2Done{Spec: spec, Verdict: VerdictHalt, Steps: steps, Ones: ones, Space: space})
			fmt.Fprintf(os.Stderr, "  halt %s %d %d %d\n", spec, steps, ones, space)
		default:
			res.Unknown++
			res.noteOpen(spec + " (" + r.Note + ")")
			fmt.Fprintf(os.Stderr, "  unknown %s (%s)\n", spec, r.Note)
		}
	}
	walk()
	res.Proved = res.Unknown == 0 && res.Halted > 0
	return res
}

func (r *BB2Result) noteOpen(spec string) {
	if len(r.Open) < 8 {
		r.Open = append(r.Open, spec)
	}
}

func (r *BB2Result) noteHalt(spec string, steps, ones, space int) {
	sc := BB2Score{Spec: spec, Steps: uint64(steps), Ones: ones, Space: space}
	if r.Halted == 1 || sc.Steps > r.Steps.Steps || (sc.Steps == r.Steps.Steps && sc.Ones > r.Steps.Ones) {
		r.Steps = sc
	}
	if r.Halted == 1 || sc.Ones > r.Ones.Ones || (sc.Ones == r.Ones.Ones && sc.Steps > r.Ones.Steps) {
		r.Ones = sc
	}
	if r.Halted == 1 || sc.Space > r.Space.Space || (sc.Space == r.Space.Space && sc.Steps > r.Space.Steps) {
		r.Space = sc
	}
}

func treeScore(form string) (steps, ones, space int, ok bool) {
	t, err := ParseTree(form)
	if err != nil {
		return 0, 0, 0, false
	}
	return scoresOf(t)
}

func treeNeed(form string) (state, sym int, ok bool) {
	t, err := ParseTree(form)
	if err != nil {
		return 0, 0, false
	}
	return needOf(t)
}

// bb2Term is the term for one machine. A closed non-halting table reduces
// to ω ω and the simulator is discarded. Otherwise the simulator runs.
func bb2Term(m Machine) *treeTerm {
	sim := tApp(tApp(zFix(bb2Driver()), bb2Move(m)), bb2Start())
	sel := tApp(onBit(treeI(), bb2Discard()), bbClosedBit(m))
	return tApp(sel, sim)
}

// bb2Driver is λself λmove λcfg. triage(ω ω, wait(self, move), K) (move cfg).
// A leaf result becomes ω ω. A stem continues with its payload. K keeps
// the payload of a fork: the score triple, or the undefined read.
// wait(self, move) is a value, so the recursive copy does not unfold
// while move cfg is still reducing.
func bb2Driver() *treeTerm {
	self, move, cfg := 0, 1, 2
	ww := tApp(treeOmega(), treeOmega())
	cont := lamS2(lamS2(lamK1(lvar(self)), lamK1(lvar(move))), lval(treeI()))
	body := lapp(ltriage(lval(ww), cont, lval(treeK())), lapp(lvar(move), lvar(cfg)))
	return compileLam(lams([]int{self, move, cfg}, body))
}

// bb2Discard is λs. (K (ω ω)) leaf. The bound variable is unused, so this
// compiles to K of that application: rule 1 drops the simulator.
func bb2Discard() *treeTerm {
	g := &lamGen{}
	s := g.id()
	body := lapp(lapp(lval(treeK()), lval(tApp(treeOmega(), treeOmega()))), lval(tLeaf()))
	return compileLam(lamAbs(s, body))
}

// bbClosedBit reduces to true when every slot is a step. For the 2-state
// walk the first transition is 1RB, so state B is reachable and this is
// the closed non-halting graph.
func bbClosedBit(m Machine) *treeTerm {
	a0 := bbIsStep(transSlot(m, 0, 0))
	a1 := bbIsStep(transSlot(m, 0, 1))
	b0 := bbIsStep(transSlot(m, 1, 0))
	b1 := bbIsStep(transSlot(m, 1, 1))
	return bbAnd(a0, bbAnd(a1, bbAnd(b0, b1)))
}

func bbIsStep(slot *treeTerm) *treeTerm {
	fals := tLeaf()
	return tApp(triage(fals, k1(fals), k1(k1(bit1()))), slot)
}

func bbAnd(a, b *treeTerm) *treeTerm {
	return tApp(onBit(tLeaf(), b), a)
}

// bb2Start is the blank tape plus loop-check memory.
// meta is cons(fresh, cons(side, cons(hist, slots))).
// fresh is true on the step after a move onto a new cell.
// side is true when that move was to the right.
// hist holds four tape snapshots. slots holds one inward record for each
// side and state: leaf if absent, otherwise cons(in1, cons(cur, max)).
func bb2Start() *treeTerm {
	z := tLeaf()
	hist := cons(z, cons(z, cons(z, z)))
	slots := cons(cons(z, z), cons(z, z))
	meta := cons(z, cons(z, cons(hist, slots)))
	return cons(initialCfg(), meta)
}

// bb2Move is one step of the blank-tape simulator, including the loop
// check. Large pieces (the inner step, equality, the record check) are
// arguments of shallow functions and each is used once. A continuation
// that mentioned a large term and also a data variable was being copied
// by bracket abstraction on every uncons layer.
func bb2Move(m Machine) *treeTerm {
	return bbAppsT(bbMoveShell(), bbNF(stepTerm(m)), bbListEq(), bbNumEq(), bbMatch())
}

func bbDup(x *lam) *lam { return lapp(lval(bbPairDup()), x) }

func bbAppsT(fn *treeTerm, args ...*treeTerm) *treeTerm {
	for _, a := range args {
		fn = tApp(fn, a)
	}
	return fn
}

func (g *lamGen) dup(v *lam, k func(*lam, *lam) *lam) *lam {
	return g.uncons(lapp(lval(bbPairDup()), v), k)
}

// bbNF reduces t to a value. Helpers are normalized before they are
// embedded so an unapplied fixpoint cannot unfold while a sibling runs.
func bbNF(t *treeTerm) *treeTerm {
	out, ok := bbTryNF(t, 20000)
	if !ok {
		panic("bbNF: term did not reach a value")
	}
	return out
}

func bbTryNF(t *treeTerm, limit int) (*treeTerm, bool) {
	for i := 0; i < limit; i++ {
		nxt, red := t.parReduct()
		if !red {
			return t, true
		}
		t = nxt
	}
	return t, false
}

func bbOnce(slot **treeTerm, build func() *treeTerm) *treeTerm {
	if *slot == nil {
		*slot = build()
	}
	return *slot
}

// bbMoveShell is λstep λeq λnum λmatch λouter.
// The loop check reduces to a value before the inner step is applied.
// uncons is a triage, so it does not copy that check while it runs.
func bbMoveShell() *treeTerm {
	return bbOnce(&bbMoveShellV, func() *treeTerm {
		g := &lamGen{}
		step, eq, num, match, outer := g.id(), g.id(), g.id(), g.id(), g.id()
		body := g.dup(lvar(eq), func(eqA, eqC *lam) *lam {
			an := bbApps(lval(bbAnalyze()), eqA, lvar(match), lvar(outer))
			return g.uncons(an, func(bit, rest *lam) *lam {
				return g.uncons(rest, func(snap, r2 *lam) *lam {
					return g.uncons(r2, func(cfg, r3 *lam) *lam {
						return g.uncons(r3, func(hist, slots *lam) *lam {
							goOn := bbApps(lval(bbRun()), lvar(step), eqC, lvar(num), snap, cfg, hist, slots)
							return ifBit(bit, goOn, lval(tLeaf()))
						})
					})
				})
			})
		})
		return compileLam(lams([]int{step, eq, num, match, outer}, body))
	})
}

var bbMoveShellV *treeTerm

// bbAnalyze is λeq λmatch λouter. cons(loopBit, cons(snap, cons(cfg, cons(hist, slots)))).
func bbAnalyze() *treeTerm {
	return bbOnce(&bbAnalyzeV, func() *treeTerm {
		g := &lamGen{}
		eq, match, outer := g.id(), g.id(), g.id()
		k := lapp(lapp(lval(bbAnalyzeGo()), lvar(eq)), lvar(match))
		body := lapp(lapp(lval(bbUnpackOuter()), k), lvar(outer))
		return compileLam(lams([]int{eq, match, outer}, body))
	})
}

var bbAnalyzeV *treeTerm

func bbUnpackOuter() *treeTerm {
	return bbOnce(&bbUnpackOuterV, func() *treeTerm {
		g := &lamGen{}
		k, outer := g.id(), g.id()
		body := g.uncons(lvar(outer), func(cfg, meta *lam) *lam {
			return g.uncons(meta, func(fresh, meta2 *lam) *lam {
				return g.uncons(meta2, func(side, meta3 *lam) *lam {
					return g.uncons(meta3, func(hist, slots *lam) *lam {
						return bbApps(lvar(k), cfg, fresh, side, hist, slots)
					})
				})
			})
		})
		return bbNF(compileLam(lams([]int{k, outer}, body)))
	})
}

var bbUnpackOuterV *treeTerm

func bbAnalyzeGo() *treeTerm {
	return bbOnce(&bbAnalyzeGoV, func() *treeTerm {
		g := &lamGen{}
		eq, match, cfg, fresh, side, hist, slots := g.id(), g.id(), g.id(), g.id(), g.id(), g.id(), g.id()
		body := g.dup(lvar(cfg), func(cfgV, cfgP *lam) *lam {
			return g.dup(lvar(side), func(sideV, sideC *lam) *lam {
				return g.dup(lvar(hist), func(histH, histP *lam) *lam {
					view := lapp(lapp(lval(bbView()), cfgV), sideV)
					return g.uncons(view, func(snap, rest *lam) *lam {
						return g.uncons(rest, func(state, rest2 *lam) *lam {
							return g.uncons(rest2, func(sym, in1 *lam) *lam {
								return g.dup(snap, func(snapH, snapP *lam) *lam {
									looked := bbApps(lval(bbConsider()), lval(bbSlotShell()), lvar(match), lvar(slots), sideC, state, sym, in1, lvar(fresh))
									return g.uncons(looked, func(bit, slots2 *lam) *lam {
										hit := bbApps(lval(bbHist()), lvar(eq), histH, snapH)
										return lcons(bbOr(hit, bit), lcons(snapP, lcons(cfgP, lcons(histP, slots2))))
									})
								})
							})
						})
					})
				})
			})
		})
		return compileLam(lams([]int{eq, match, cfg, fresh, side, hist, slots}, body))
	})
}

var bbAnalyzeGoV *treeTerm

func bbApps(fn *lam, args ...*lam) *lam {
	for _, a := range args {
		fn = lapp(fn, a)
	}
	return fn
}

func bbOr(a, b *lam) *lam {
	return ifBit(a, b, lval(bit1()))
}

func bbNot(a *lam) *lam { return lapp(lval(treeNot()), a) }

// bbRun is λstep λeq λnum λsnap λcfg λhist λslots.
// A fork from the inner step is the halt or need value, passed through.
// A stem is the next tape. The loop bit has already been decided, and this
// function is the arm triage keeps until that bit is a value.
func bbRun() *treeTerm {
	return bbOnce(&bbRunV, func() *treeTerm {
		g := &lamGen{}
		step, eq, num, snap, cfg, hist, slots := g.id(), g.id(), g.id(), g.id(), g.id(), g.id(), g.id()
		body := g.dup(lvar(cfg), func(cfgS, cfgF *lam) *lam {
			applied := lapp(lvar(step), cfgS)
			return g.shape(applied,
				lval(tLeaf()),
				func(newCfg *lam) *lam {
					return bbApps(lval(bbFinish()), lvar(eq), lvar(num), cfgF, newCfg, lvar(hist), lvar(snap), lvar(slots))
				},
				func(a, b *lam) *lam { return lcons(a, b) },
			)
		})
		return compileLam(lams([]int{step, eq, num, snap, cfg, hist, slots}, body))
	})
}

var bbRunV *treeTerm

func bbFinish() *treeTerm {
	return bbOnce(&bbFinishV, func() *treeTerm {
		g := &lamGen{}
		eq, num, old, neu, hist, snap, slots := g.id(), g.id(), g.id(), g.id(), g.id(), g.id(), g.id()
		body := g.dup(lvar(neu), func(neuE, neuR *lam) *lam {
			return g.dup(lvar(num), func(numG, numB *lam) *lam {
				return g.uncons(lapp(lval(bbEnds()), lvar(old)), func(oldLeft, oldSp *lam) *lam {
					return g.uncons(lapp(lval(bbEnds()), neuE), func(newLeft, newSp *lam) *lam {
						moved := bbApps(lval(bbMovedShell()), lvar(eq), oldLeft, newLeft)
						grew := bbApps(lval(bbGrewShell()), numG, oldSp, newSp)
						return g.dup(moved, func(mDir, mSide *lam) *lam {
							slots2 := bbApps(lval(bbBumpAll()), lapp(lval(bbBumpShell()), numB), lvar(slots), mDir)
							hist2 := lapp(lapp(lval(bbHistPush()), lvar(hist)), lvar(snap))
							meta := lcons(grew, lcons(mSide, lcons(hist2, slots2)))
							return lstem(lcons(neuR, meta))
						})
					})
				})
			})
		})
		return compileLam(lams([]int{eq, num, old, neu, hist, snap, slots}, body))
	})
}

var bbFinishV *treeTerm

func bbPairDup() *treeTerm {
	g := &lamGen{}
	x := g.id()
	return compileLam(lamAbs(x, lcons(lvar(x), lvar(x))))
}

func bbQuad() *treeTerm {
	g := &lamGen{}
	x := g.id()
	return compileLam(lamAbs(x, lcons(lvar(x), lcons(lvar(x), lcons(lvar(x), lvar(x))))))
}

// bbView returns cons(snap, cons(state, cons(sym, in1))).
// in1 is the cell one step inward of a fresh extreme: the left list when
// the extreme is on the right, and the right list otherwise.
func bbView() *treeTerm {
	g := &lamGen{}
	cfg, side := g.id(), g.id()
	body := g.uncons(lvar(cfg), func(st, r1 *lam) *lam {
		return g.uncons(r1, func(sy, r2 *lam) *lam {
			return g.uncons(r2, func(rr, r3 *lam) *lam {
				return g.uncons(r3, func(left, _ *lam) *lam {
					return g.uncons(bbDup(st), func(st1, st2 *lam) *lam {
						return g.uncons(bbDup(sy), func(sy1, sy2 *lam) *lam {
							return g.uncons(bbDup(left), func(l1, l2 *lam) *lam {
								return g.uncons(bbDup(rr), func(rr1, rr2 *lam) *lam {
									in1 := ifBit(lvar(side), lapp(lval(bbHead()), rr1), lapp(lval(bbHead()), l1))
									snap := lcons(st1, lcons(sy1, lcons(l2, rr2)))
									return lcons(snap, lcons(st2, lcons(sy2, in1)))
								})
							})
						})
					})
				})
			})
		})
	})
	return compileLam(lams([]int{cfg, side}, body))
}

func bbHead() *treeTerm {
	g := &lamGen{}
	list := g.id()
	body := g.shape(lvar(list),
		lval(tLeaf()),
		func(*lam) *lam { return lval(tLeaf()) },
		func(h, _ *lam) *lam { return h },
	)
	return compileLam(lamAbs(list, body))
}

func bbEnds() *treeTerm {
	g := &lamGen{}
	cfg := g.id()
	body := g.uncons(lvar(cfg), func(_, r1 *lam) *lam {
		return g.uncons(r1, func(_, r2 *lam) *lam {
			return g.uncons(r2, func(_, r3 *lam) *lam {
				return g.uncons(r3, func(left, r4 *lam) *lam {
					return g.uncons(r4, func(_, r5 *lam) *lam {
						return g.uncons(r5, func(_, space *lam) *lam {
							return lcons(left, space)
						})
					})
				})
			})
		})
	})
	return compileLam(lamAbs(cfg, body))
}

// bbConsider is λslotFn λmatch λslots λside λstate λsym λin1 λfresh.
// cons(loopBit, slots). The unpacker applies its continuation once, so the
// slot function is not copied into every uncons layer.
func bbConsider() *treeTerm {
	return bbOnce(&bbConsiderV, func() *treeTerm {
		g := &lamGen{}
		slotFn, match, slots, side, state, sym, in1, fresh := g.id(), g.id(), g.id(), g.id(), g.id(), g.id(), g.id(), g.id()
		// split returns λslotFn λmatch λside λstate λsym λin1 λfresh. join
		got := lapp(lapp(lval(bbSplitSlots()), lval(bbConsiderAll())), lvar(slots))
		body := bbApps(got, lvar(slotFn), lvar(match), lvar(side), lvar(state), lvar(sym), lvar(in1), lvar(fresh))
		return compileLam(lams([]int{slotFn, match, slots, side, state, sym, in1, fresh}, body))
	})
}

func bbSplitSlots() *treeTerm {
	return bbOnce(&bbSplitSlotsV, func() *treeTerm {
		g := &lamGen{}
		k, slots := g.id(), g.id()
		body := g.uncons(lvar(slots), func(rp, lp *lam) *lam {
			return g.uncons(rp, func(r0, r1 *lam) *lam {
				return g.uncons(lp, func(l0, l1 *lam) *lam {
					return bbApps(lvar(k), r0, r1, l0, l1)
				})
			})
		})
		return compileLam(lams([]int{k, slots}, body))
	})
}

var bbSplitSlotsV *treeTerm

func bbConsiderAll() *treeTerm {
	return bbOnce(&bbConsiderAllV, func() *treeTerm {
		g := &lamGen{}
		r0, r1, l0, l1 := g.id(), g.id(), g.id(), g.id()
		slotFn, match := g.id(), g.id()
		side, state, sym, in1, fresh := g.id(), g.id(), g.id(), g.id(), g.id()
		a := bbSlotCall(lvar(slotFn), lvar(match), lvar(r0), lvar(side), lvar(state), lvar(sym), lvar(in1), lvar(fresh), bit1(), tLeaf())
		b := bbSlotCall(lvar(slotFn), lvar(match), lvar(r1), lvar(side), lvar(state), lvar(sym), lvar(in1), lvar(fresh), bit1(), bit1())
		c := bbSlotCall(lvar(slotFn), lvar(match), lvar(l0), lvar(side), lvar(state), lvar(sym), lvar(in1), lvar(fresh), tLeaf(), tLeaf())
		d := bbSlotCall(lvar(slotFn), lvar(match), lvar(l1), lvar(side), lvar(state), lvar(sym), lvar(in1), lvar(fresh), tLeaf(), bit1())
		body := bbApps(lval(bbJoin4()), a, b, c, d)
		// Multi-use names are bound while the four calls are still small.
		// r0..l1 are bound afterwards; each occurs once.
		acc := body
		for _, id := range []int{fresh, in1, sym, state, side, match, slotFn} {
			acc = lamAbs(id, acc)
		}
		acc = lamAbs(l1, acc)
		acc = lamAbs(l0, acc)
		acc = lamAbs(r1, acc)
		acc = lamAbs(r0, acc)
		return compileLam(acc)
	})
}

var bbConsiderAllV *treeTerm

var bbConsiderV *treeTerm

func (g *lamGen) quad(v *lam, k func(a, b, c, d *lam) *lam) *lam {
	return g.uncons(lapp(lval(bbQuad()), v), func(a, r *lam) *lam {
		return g.uncons(r, func(b, r2 *lam) *lam {
			return g.uncons(r2, func(c, d *lam) *lam {
				return k(a, b, c, d)
			})
		})
	})
}

func bbSlotCall(slotFn, match, slot, side, state, sym, in1, fresh *lam, wantSide, wantState *treeTerm) *lam {
	return bbApps(slotFn, match, slot, side, state, sym, in1, fresh, lval(wantSide), lval(wantState))
}

func bbJoin4() *treeTerm {
	return bbOnce(&bbJoin4V, func() *treeTerm {
		g := &lamGen{}
		a, b, c, d := g.id(), g.id(), g.id(), g.id()
		body := bbJoin(g, lvar(a), lvar(b), lvar(c), lvar(d))
		return compileLam(lams([]int{a, b, c, d}, body))
	})
}

var bbJoin4V *treeTerm

// bbJoin ors four cons(bit, slot) results into cons(or, slots).
func bbJoin(g *lamGen, a, b, c, d *lam) *lam {
	return g.uncons(a, func(ba, sa *lam) *lam {
		return g.uncons(b, func(bb, sb *lam) *lam {
			return g.uncons(c, func(bc, sc *lam) *lam {
				return g.uncons(d, func(bd, sd *lam) *lam {
					bit := bbOr(ba, bbOr(bb, bbOr(bc, bd)))
					return lcons(bit, lcons(lcons(sa, sb), lcons(sc, sd)))
				})
			})
		})
	})
}

// bbSlotShell is λmatch λslot λside λstate λsym λin1 λfresh λwantSide λwantState.
// cons(loop, slot). Only the slot whose side and state match can loop
// or be replaced with a new record.
func bbSlotShell() *treeTerm {
	return bbOnce(&bbSlotShellV, func() *treeTerm {
		g := &lamGen{}
		match, slot, side, state, sym, in1, fresh := g.id(), g.id(), g.id(), g.id(), g.id(), g.id(), g.id()
		wantSide, wantState := g.id(), g.id()
		sideOK := lapp(lapp(lval(bbBitEq()), lvar(side)), lvar(wantSide))
		stateOK := lapp(lapp(lval(bbBitEq()), lvar(state)), lvar(wantState))
		selected := bbAndL(sideOK, stateOK)
		matched := bbApps(lvar(match), lvar(slot), lvar(sym), lvar(in1))
		body := g.let(matched, func(m *lam) *lam {
			return g.let(selected, func(sel *lam) *lam {
				looped := bbAndL(lvar(fresh), bbAndL(sel, m))
				replace := bbAndL(lvar(fresh), bbAndL(sel, bbNot(m)))
				rec := lapp(lval(bbRecord()), lvar(in1))
				out := ifBit(replace, lvar(slot), rec)
				return lcons(looped, out)
			})
		})
		return compileLam(lams([]int{match, slot, side, state, sym, in1, fresh, wantSide, wantState}, body))
	})
}

var bbSlotShellV *treeTerm

func (g *lamGen) let(val *lam, k func(*lam) *lam) *lam {
	v := g.id()
	return lapp(lamAbs(v, k(lvar(v))), val)
}

func bbAndL(a, b *lam) *lam {
	return ifBit(a, lval(tLeaf()), b)
}

func bbRecord() *treeTerm {
	g := &lamGen{}
	in1 := g.id()
	body := lcons(lvar(in1), lcons(lval(tLeaf()), lval(tLeaf())))
	return compileLam(lamAbs(in1, body))
}

// bbMatch reports whether this fresh extreme repeats the stored record
// with inward distance 0 or 1 and a blank head. A missing record is not
// a loop. Distance above 1 is not a loop: the check under-approximates.
func bbMatch() *treeTerm {
	return bbOnce(&bbMatchV, func() *treeTerm {
		g := &lamGen{}
		slot, sym, in1 := g.id(), g.id(), g.id()
		fail := lval(tLeaf())
		body := g.shape(lvar(slot),
			fail,
			func(*lam) *lam { return fail },
			func(stored, rest *lam) *lam {
				return g.uncons(rest, func(_, max *lam) *lam {
					// L = 0 loops on a blank head.
					l0 := ifBit(lvar(sym), lval(bit1()), fail)
					return g.shape(max,
						l0,
						func(m1 *lam) *lam {
							// L = 1 loops on a blank head whose inward cell matches.
							one := ifBit(lapp(lapp(lval(bbBitEq()), stored), lvar(in1)), fail, lval(bit1()))
							l1 := ifBit(lvar(sym), one, fail)
							return g.shape(m1,
								l1,
								func(*lam) *lam { return fail },
								func(*lam, *lam) *lam { return fail },
							)
						},
						func(*lam, *lam) *lam { return fail },
					)
				})
			},
		)
		return bbNF(compileLam(lams([]int{slot, sym, in1}, body)))
	})
}

var bbMatchV *treeTerm

// bbBumpAll is λbump λslots λmoved.
// Right-hand records move inward when the head moved left.
// Left-hand records move inward when the head moved right.
func bbBumpAll() *treeTerm {
	return bbOnce(&bbBumpAllV, func() *treeTerm {
		g := &lamGen{}
		bump, slots, moved := g.id(), g.id(), g.id()
		body := g.dup(lvar(bump), func(bR, bL *lam) *lam {
			return g.dup(lvar(moved), func(mvR, mvL *lam) *lam {
				return g.uncons(lvar(slots), func(rp, lp *lam) *lam {
					rb := bbApps(lval(bbBumpPair()), bR, rp, bbNot(mvR))
					lb := bbApps(lval(bbBumpPair()), bL, lp, mvL)
					return lcons(rb, lb)
				})
			})
		})
		return compileLam(lams([]int{bump, slots, moved}, body))
	})
}

var bbBumpAllV *treeTerm

func bbBumpPair() *treeTerm {
	return bbOnce(&bbBumpPairV, func() *treeTerm {
		g := &lamGen{}
		bump, pair, inward := g.id(), g.id(), g.id()
		body := g.dup(lvar(bump), func(b0, b1 *lam) *lam {
			return g.dup(lvar(inward), func(i0, i1 *lam) *lam {
				return g.uncons(lvar(pair), func(s0, s1 *lam) *lam {
					return lcons(bbApps(b0, s0, i0), bbApps(b1, s1, i1))
				})
			})
		})
		return compileLam(lams([]int{bump, pair, inward}, body))
	})
}

var bbBumpPairV *treeTerm

// bbBumpShell is λnum λslot λinward.
// An absent record stays absent. Moving inward increments cur and, when
// cur was max, increments max. Moving outward decrements cur. pred(0) is 0.
func bbBumpShell() *treeTerm {
	return bbOnce(&bbBumpShellV, func() *treeTerm {
		g := &lamGen{}
		num, slot, inward := g.id(), g.id(), g.id()
		body := g.shape(lvar(slot),
			lval(tLeaf()),
			func(*lam) *lam { return lval(tLeaf()) },
			func(in1, rest *lam) *lam {
				return g.uncons(rest, func(cur, max *lam) *lam {
					eq := lapp(lapp(lvar(num), cur), max)
					nmax := ifBit(eq, max, lapp(lval(tLeaf()), max))
					outward := lcons(in1, lcons(lapp(lval(predFn()), cur), max))
					inw := lcons(in1, lcons(lapp(lval(tLeaf()), cur), nmax))
					return ifBit(lvar(inward), outward, inw)
				})
			},
		)
		return compileLam(lams([]int{num, slot, inward}, body))
	})
}

var bbBumpShellV *treeTerm

func bbMovedShell() *treeTerm {
	return bbOnce(&bbMovedShellV, func() *treeTerm {
		g := &lamGen{}
		eq, old, neu := g.id(), g.id(), g.id()
		body := g.shape(lvar(neu),
			lval(tLeaf()),
			func(*lam) *lam { return lval(tLeaf()) },
			func(_, t *lam) *lam { return lapp(lapp(lvar(eq), t), lvar(old)) },
		)
		return compileLam(lams([]int{eq, old, neu}, body))
	})
}

var bbMovedShellV *treeTerm

func bbGrewShell() *treeTerm {
	return bbOnce(&bbGrewShellV, func() *treeTerm {
		g := &lamGen{}
		num, old, neu := g.id(), g.id(), g.id()
		body := g.shape(lvar(neu),
			lval(tLeaf()),
			func(p *lam) *lam { return lapp(lapp(lvar(num), p), lvar(old)) },
			func(*lam, *lam) *lam { return lval(tLeaf()) },
		)
		return compileLam(lams([]int{num, old, neu}, body))
	})
}

var bbGrewShellV *treeTerm

// bbHist is λeq λhist λsnap. True when snap equals one of four history slots.
// A leaf slot is never equal to a real snapshot.
func bbHist() *treeTerm {
	return bbOnce(&bbHistV, func() *treeTerm {
		g := &lamGen{}
		eq, hist, snap := g.id(), g.id(), g.id()
		got := lapp(lapp(lapp(lval(bbUnpackHist()), lval(bbHistGo())), lvar(hist)), lvar(snap))
		body := lapp(lapp(got, lval(bbSnapShell())), lvar(eq))
		return compileLam(lams([]int{eq, hist, snap}, body))
	})
}

var bbHistV *treeTerm

func bbUnpackHist() *treeTerm {
	return bbOnce(&bbUnpackHistV, func() *treeTerm {
		g := &lamGen{}
		k, hist, snap := g.id(), g.id(), g.id()
		body := g.quad(lvar(snap), func(s0, s1, s2, s3 *lam) *lam {
			return g.uncons(lvar(hist), func(h0, r1 *lam) *lam {
				return g.uncons(r1, func(h1, r2 *lam) *lam {
					return g.uncons(r2, func(h2, h3 *lam) *lam {
						return bbApps(lvar(k), h0, h1, h2, h3, s0, s1, s2, s3)
					})
				})
			})
		})
		return compileLam(lams([]int{k, hist, snap}, body))
	})
}

var bbUnpackHistV *treeTerm

func bbHistGo() *treeTerm {
	return bbOnce(&bbHistGoV, func() *treeTerm {
		g := &lamGen{}
		snapFn, eq := g.id(), g.id()
		h0, h1, h2, h3 := g.id(), g.id(), g.id(), g.id()
		s0, s1, s2, s3 := g.id(), g.id(), g.id(), g.id()
		q0 := bbApps(lvar(snapFn), lvar(eq), lvar(h0), lvar(s0))
		q1 := bbApps(lvar(snapFn), lvar(eq), lvar(h1), lvar(s1))
		q2 := bbApps(lvar(snapFn), lvar(eq), lvar(h2), lvar(s2))
		q3 := bbApps(lvar(snapFn), lvar(eq), lvar(h3), lvar(s3))
		body := bbOr(q0, bbOr(q1, bbOr(q2, q3)))
		// snapFn and eq are used four times. Bind them before the fields so
		// the split does not copy a term that is already wrapped.
		acc := lamAbs(eq, body)
		acc = lamAbs(snapFn, acc)
		return compileLam(lams([]int{h0, h1, h2, h3, s0, s1, s2, s3}, acc))
	})
}

var bbHistGoV *treeTerm

func bbHistPush() *treeTerm {
	g := &lamGen{}
	hist, snap := g.id(), g.id()
	body := g.uncons(lvar(hist), func(h0, r1 *lam) *lam {
		return g.uncons(r1, func(h1, r2 *lam) *lam {
			return g.uncons(r2, func(h2, _ *lam) *lam {
				return lcons(lvar(snap), lcons(h0, lcons(h1, h2)))
			})
		})
	})
	return compileLam(lams([]int{hist, snap}, body))
}

func bbSnapShell() *treeTerm {
	return bbOnce(&bbSnapShellV, func() *treeTerm {
		g := &lamGen{}
		eq, a, b := g.id(), g.id(), g.id()
		fail := lval(tLeaf())
		body := g.shape(lvar(a),
			fail,
			func(*lam) *lam { return fail },
			func(s1, r1 *lam) *lam {
				return g.shape(lvar(b),
					fail,
					func(*lam) *lam { return fail },
					func(s2, r2 *lam) *lam {
						return g.uncons(r1, func(y1, r1b *lam) *lam {
							return g.uncons(r2, func(y2, r2b *lam) *lam {
								return g.uncons(r1b, func(l1, rr1 *lam) *lam {
									return g.uncons(r2b, func(l2, rr2 *lam) *lam {
										return g.dup(lvar(eq), func(eL, eR *lam) *lam {
											es := lapp(lapp(lval(bbBitEq()), s1), s2)
											ey := lapp(lapp(lval(bbBitEq()), y1), y2)
											el := lapp(lapp(eL, l1), l2)
											er := lapp(lapp(eR, rr1), rr2)
											return bbAndL(es, bbAndL(ey, bbAndL(el, er)))
										})
									})
								})
							})
						})
					},
				)
			},
		)
		return compileLam(lams([]int{eq, a, b}, body))
	})
}

var bbSnapShellV *treeTerm

func bbBitEq() *treeTerm {
	g := &lamGen{}
	a, b := g.id(), g.id()
	no := ifBit(lvar(b), lval(bit1()), lval(tLeaf()))
	yes := ifBit(lvar(b), lval(tLeaf()), lval(bit1()))
	body := ifBit(lvar(a), no, yes)
	return compileLam(lams([]int{a, b}, body))
}

func bbListEq() *treeTerm {
	return bbOnce(&bbListEqV, func() *treeTerm {
		g := &lamGen{}
		a, b := g.id(), g.id()
		body := bbEqList(g, lvar(a), lvar(b), 8)
		return bbNF(compileLam(lams([]int{a, b}, body)))
	})
}

var bbListEqV *treeTerm

func bbNumEq() *treeTerm {
	return bbOnce(&bbNumEqV, func() *treeTerm {
		g := &lamGen{}
		a, b := g.id(), g.id()
		body := bbEqNum(g, lvar(a), lvar(b), 16)
		return bbNF(compileLam(lams([]int{a, b}, body)))
	})
}

var bbNumEqV *treeTerm

func bbEqList(g *lamGen, a, b *lam, depth int) *lam {
	tru := lval(bit1())
	fail := lval(tLeaf())
	if depth == 0 {
		return g.shape(a,
			g.shape(b, tru, func(*lam) *lam { return fail }, func(*lam, *lam) *lam { return fail }),
			func(*lam) *lam { return fail },
			func(*lam, *lam) *lam { return fail },
		)
	}
	return g.shape(a,
		g.shape(b, tru, func(*lam) *lam { return fail }, func(*lam, *lam) *lam { return fail }),
		func(*lam) *lam { return fail },
		func(ha, ta *lam) *lam {
			return g.shape(b,
				fail,
				func(*lam) *lam { return fail },
				func(hb, tb *lam) *lam {
					eq := lapp(lapp(lval(bbBitEq()), ha), hb)
					return ifBit(eq, fail, bbEqList(g, ta, tb, depth-1))
				},
			)
		},
	)
}

func bbEqNum(g *lamGen, a, b *lam, depth int) *lam {
	tru := lval(bit1())
	fail := lval(tLeaf())
	if depth == 0 {
		return g.shape(a,
			g.shape(b, tru, func(*lam) *lam { return fail }, func(*lam, *lam) *lam { return fail }),
			func(*lam) *lam { return fail },
			func(*lam, *lam) *lam { return fail },
		)
	}
	return g.shape(a,
		g.shape(b, tru, func(*lam) *lam { return fail }, func(*lam, *lam) *lam { return fail }),
		func(a2 *lam) *lam {
			return g.shape(b,
				fail,
				func(b2 *lam) *lam { return bbEqNum(g, a2, b2, depth-1) },
				func(*lam, *lam) *lam { return fail },
			)
		},
		func(*lam, *lam) *lam { return fail },
	)
}
