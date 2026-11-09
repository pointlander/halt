// Copyright 2026 The Halt Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "testing"

// TestSolveBB2 is the tree proof of the 2-state blank-tape machines.
// SolveBB2 does not call the simulator. This test checks each tree halt
// against simulation and each tree loop against the other decider.
func TestSolveBB2(t *testing.T) {
	res := SolveBB2()
	t.Log(res.Text())
	if !res.Proved || res.Unknown != 0 {
		t.Fatalf("not proved: %s open %v", res.Text(), res.Open)
	}
	var halted, looping int
	var maxSteps uint64
	var maxOnes, maxSpace int
	for _, d := range res.Done {
		m, err := Parse(d.Spec)
		if err != nil {
			t.Fatal(err)
		}
		switch d.Verdict {
		case VerdictHalt:
			halted++
			sim := Simulate(m, 100)
			if sim.Verdict != VerdictHalt || int(sim.Steps) != d.Steps || sim.Ones != d.Ones || sim.Space != d.Space {
				t.Fatalf("%s tree %d %d %d sim steps %d ones %d space %d verdict %v",
					d.Spec, d.Steps, d.Ones, d.Space, sim.Steps, sim.Ones, sim.Space, sim.Verdict)
			}
			if uint64(d.Steps) > maxSteps {
				maxSteps = uint64(d.Steps)
			}
			if d.Ones > maxOnes {
				maxOnes = d.Ones
			}
			if d.Space > maxSpace {
				maxSpace = d.Space
			}
		case VerdictLoop:
			looping++
			o := Decide(m, 100)
			if o.Verdict != VerdictLoop {
				t.Fatalf("%s tree loop, decide %v", d.Spec, o.Verdict)
			}
		default:
			t.Fatalf("%s verdict %v", d.Spec, d.Verdict)
		}
	}
	if halted != res.Halted || looping != res.Looping {
		t.Fatalf("done halt %d loop %d result halt %d loop %d", halted, looping, res.Halted, res.Looping)
	}
	if halted != 30 || looping != 106 {
		t.Fatalf("settled halt %d loop %d", halted, looping)
	}
	if res.Steps.Steps != maxSteps || res.Ones.Ones != maxOnes || res.Space.Space != maxSpace {
		t.Fatalf("extremes steps %d ones %d space %d max %d %d %d",
			res.Steps.Steps, res.Ones.Ones, res.Space.Space, maxSteps, maxOnes, maxSpace)
	}
	witness, err := Parse(res.Steps.Spec)
	if err != nil {
		t.Fatal(err)
	}
	sim := Simulate(witness, 100)
	if sim.Verdict != VerdictHalt || sim.Steps != res.Steps.Steps || sim.Ones != res.Steps.Ones || sim.Space != res.Steps.Space {
		t.Fatalf("step witness %s sim %d %d %d", res.Steps.Spec, sim.Steps, sim.Ones, sim.Space)
	}
}
