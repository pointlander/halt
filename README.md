# halt

A partial decider for the blank-tape halting problem, with the busy beaver functions as the worked example.

No algorithm answers, for every Turing machine, whether it halts. `halt` proves the cases it can and says **unknown** otherwise. A halt verdict is a simulation witness. A loop verdict is a proof:

- the same configuration repeats (a cycler)
- a record-breaking configuration repeats, shifted in space (a translated cycler)
- every reachable transition is defined and none of them halts
- a bouncer inserts one more copy of a block on every pass
- a binary counter adds one cell each time it overflows
- a proved program-size cutoff is past and the machine is still running (`halt k`)
- every path into a halting read contradicts within the steps already run (`halt stat`)
- a tree-calculus term reaches a value, or it is an application of two ω-blocks (`halt tree`)

S(n) is the longest a halting n-state 2-symbol machine can run. Σ(n) is the most 1s one can leave. Both are uncomputable. This program computes them for small n by deciding machines, not by looking up the published values.

## Build

Go 1.27 or later.

```sh
go test
go run .
go build -o halt .
```

## Machines

The model is the busy-beaver one: n states, symbols `{0, 1}`, one two-way infinite tape, start in state A on a blank tape.

Transitions use the [Busy Beaver Challenge](https://bbchallenge.org) text format. `1RB` writes 1, moves right, and enters B. States are letters `A`, `B`, `C`, …. `H` and `Z` both mean halt. `---` is undefined; reaching it halts with no write and no move.

```text
1RB1LB_1LA1RH
1RB 1LB  1LA 1RH
1RH
```

The halting transition counts as a step: it writes, moves, and enters H. Space counts cells that are read. The cell reached only by that final move is not included.

Flags go before the machine. The Go `flag` package treats a later flag as part of the spec.

```sh
halt run --trace --limit 20 1RB1LB_1LA1RH
```

## Commands

```text
halt                         simulate champions and search small n
halt run SPEC [--trace] [--limit N]
halt decide SPEC [--limit N]
halt search N [--limit N]
halt k
halt k decide SPEC
halt stat
halt stat decide SPEC [--limit N]
halt tree
halt tree decide TERM [--limit N]
```

`run` only simulates. Hitting the step limit is unknown, not a loop. `decide` adds the loop proofs above, except the program-size cutoff, the state-symbol search, and tree calculus. `search` enumerates machines in tree normal form. For n > 1 the first transition is fixed as `1RB`; mirrors and state relabelings are omitted. When every machine is decided, S(n), Σ(n), and space(n) are proved. Otherwise the three scores are lower bounds from machines that did halt.

`halt k`, `halt stat`, and `halt tree` are separate solvers. See below.

## Busy beaver

`go run .` simulates these champions and searches n = 1..4.

| n | machine | steps | ones |
|---:|---|---:|---:|
| 1 | `1RH` | 1 | 1 |
| 2 | `1RB1LB_1LA1RH` | 6 | 4 |
| 3 | `1RB1RH_0RC1RB_1LC1LA` | 14 | 6 |
| 4 | `1RB1LB_1LA0LC_1RH1LD_1RD0RA` | 107 | 13 |
| 5 | `1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA` | 47,176,870 | 4,098 |

The 3-state row is a Σ champion. S(3) is 21, from `1RB1RH_1LB0RC_1LC1LA`, which leaves five 1s. Search finds that machine; it is not hardcoded.

Search proves n ≤ 3: S is 1, 6, 21; Σ is 1, 4, 6; space is 1, 4, 7. For n = 4 it finds machines with 107 steps, 13 ones, and 16 cells, and leaves some machines unknown, so those numbers are a lower bound. The 4-state step champion itself reads 14 cells. space(4) = 16 is a different machine. n = 5 is simulated, not searched.

## Program-size complexity

`halt k` decides machines from Kolmogorov complexity on one reference machine U.

A program is a prefix-free encoding of a complete transition table (every transition defined). U(p) is the number of steps p runs on a blank tape. If p halts in t steps, then K(t) is at most the bit length of p. So an L-bit program halts within Σ_H(L) steps or not at all. Σ_H(L) is the largest integer with complexity at most L.

That cutoff is a proof only when every program of length ≤ L has been decided. Here that holds through 3 states:

| states | bits | Σ_H | |
|---:|---:|---:|---|
| 1 | 7 | 1 | K(1) = 7 |
| 2 | 18 | 6 | K(6) = 18 |
| 3 | 27 | 21 | K(21) = 27 |

Past that line a halt is still a simulation witness, and K(t) ≤ L is only an upper bound. A machine that is still running stays unknown. A lower bound on Σ_H is not used as a loop proof.

```sh
halt k
halt k decide 1RA1RA
halt k decide 1RB1RH_1LB0RC_1LC1LA
```

`1RA` is rejected: `---` is not a program for U.

## State-symbol search

`halt stat` counts each forward read by state and symbol, then searches backward from every halting read. A reverse step undoes one transition. It stands when the cell that transition wrote is still unknown, or already holds that write. A different known symbol kills the branch.

If every branch contradicts by depth H, a halting read is reachable in at most H steps, so the halt itself occurs by step H+1. A blank-tape run that has already gone past that step is a loop proof. The forward counts choose which branch to expand first. Every branch is expanded, so a rare read can still be the one that halts. A tree that reaches the depth cap (32) or the node cap (100,000) stays unknown.

A halt verdict is still the forward simulation. Machines with no halting transition at all are loops at once. Published values of S(n) are not used.

```sh
halt stat
halt stat decide --limit 32 1RB1RA_0LC1RA_---1LA
halt stat decide --limit 4 1RB1LB_1LA1RH
```

The first machine's only halt is unreachable: the sole path into it writes a 1 where the path needs a 0. The second is the 2-state step champion. Four steps are not enough to pass its halting read, so the result stays unknown. Six steps halt.

## Tree calculus

`halt tree` decides terms of the triage calculus. A term is a leaf or the application of two terms. `^` is the leaf. `△` and `Δ` are the same leaf. Application is written by juxtaposition and associates to the left. Parentheses group.

The five rules are:

```text
△ △ y z             →  y
△ (△ x) y z         →  x z (y z)
△ (△ w x) y △       →  w
△ (△ w x) y (△ u)   →  x u
△ (△ w x) y (△ u v) →  y u v
```

A value, a tree with no subterm `△ a b c`, is a halt witness. The solver contracts every outermost redex in one step. The rules are left-linear and do not overlap, so that strategy reaches a value whenever the term has one. The same term appearing again is a loop. So is an application of two ω-blocks, which is how `ω ω` is decided without waiting out the cycle. `K` is `△ △`, `I` is `△ (△ K) K`, and `ω` is `△ (△ I) I`. A block is `ω`, or `I` on a block, or `K` on a block applied to `K` on a block. Applying two blocks always has a redex, and every reduct is another such application. `△ △ leaf (ω ω)` halts as the leaf, because the first rule discards the copy of `ω ω`. A search that reaches the step cap or the printed-size cap stays unknown. Reaching a value decides that term. It does not decide halting for every term, and it is not a new decision procedure for Turing machines.

The limit flag comes before the term.

```sh
halt tree
halt tree decide '^ ^ ^ ^'
halt tree decide --limit 1 '^ ^ ^ ^'
```

`^ ^ ^ ^` is `△ △ ^ ^`, which reduces to `^`.

## License

BSD 3-Clause. See [LICENSE](LICENSE).
