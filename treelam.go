// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

// lam is a combinator term before it is compiled to a tree. Variables are
// removed by bracket abstraction. A compiled value has no variables.
type lam struct {
	kind lamKind
	id   int
	fun  *lam
	arg  *lam
	val  *treeTerm
}

type lamKind int

const (
	lamVar lamKind = iota
	lamApp
	lamVal
)

func lvar(id int) *lam { return &lam{kind: lamVar, id: id} }

func lval(t *treeTerm) *lam { return &lam{kind: lamVal, val: t} }

func lapp(fun, arg *lam) *lam { return &lam{kind: lamApp, fun: fun, arg: arg} }

func lapps(ts ...*lam) *lam {
	t := ts[0]
	for _, a := range ts[1:] {
		t = lapp(t, a)
	}
	return t
}

// combS is the S combinator: S x y z reduces to x z (y z).
func combS() *treeTerm {
	// △ (△ (K △)) △
	kLeaf := tApp(treeK(), tLeaf())
	return tApp(tApp(tLeaf(), tApp(tLeaf(), kLeaf)), tLeaf())
}

func usesLam(id int, m *lam) bool {
	switch m.kind {
	case lamVar:
		return m.id == id
	case lamApp:
		return usesLam(id, m.fun) || usesLam(id, m.arg)
	default:
		return false
	}
}

// abs binds id. Eta contraction keeps the combinator small:
// [x](M x) = M when x is not free in M.
func lamAbs(id int, m *lam) *lam {
	if !usesLam(id, m) {
		return lapp(lval(treeK()), m)
	}
	if m.kind == lamApp && m.arg.kind == lamVar && m.arg.id == id && !usesLam(id, m.fun) {
		return m.fun
	}
	switch m.kind {
	case lamVar:
		return lval(treeI())
	case lamApp:
		// s2(u, v) x → u x (v x), and it is smaller than S u v.
		// A side that ignores x becomes K of that side, which is B or C.
		if !usesLam(id, m.fun) {
			return lamS2(lamK1(m.fun), lamAbs(id, m.arg))
		}
		if !usesLam(id, m.arg) {
			return lamS2(lamAbs(id, m.fun), lamK1(m.arg))
		}
		return lamS2(lamAbs(id, m.fun), lamAbs(id, m.arg))
	default:
		return lapp(lval(treeK()), m)
	}
}

// lamS2 builds the value △ (△ u) v.
func lamS2(u, v *lam) *lam {
	return lapp(lapp(lval(tLeaf()), lapp(lval(tLeaf()), u)), v)
}

// lamK1 builds K x, the value △ △ x.
func lamK1(m *lam) *lam { return lapp(lval(treeK()), m) }

func compileLam(m *lam) *treeTerm {
	switch m.kind {
	case lamVal:
		return m.val
	case lamApp:
		return tApp(compileLam(m.fun), compileLam(m.arg))
	default:
		return nil
	}
}

// turingFix is Turing's Θ applied to f: Θ = U U, U = λx y. y (x x y).
// Θ f x reduces to f (Θ f) x. A linear use of the argument is copied
// once along the reduction; f itself is copied a small constant number
// of times.
func turingFix(f *treeTerm) *treeTerm {
	x, y := 0, 1
	body := lapp(lvar(y), lapp(lapp(lvar(x), lvar(x)), lvar(y)))
	u := compileLam(lamAbs(x, lamAbs(y, body)))
	return tApp(tApp(u, u), f)
}

// yComb F reduces to F (yComb F).
func yComb(f *treeTerm) *treeTerm {
	// W = S (K F) ω, Y = W W.
	w := tApp(tApp(combS(), tApp(treeK(), f)), treeOmega())
	return tApp(w, w)
}
