/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHConstant

/-! # Inspect the original 815 L24 contributions at the strict-transform line

Run `lake env lean --run scripts/explore_bl2_line_l24.lean` to print an
index, weighted contraction and running sum for every slot. This evaluates
the original lower-genus graph without importing the candidate table or
its component cache.
-/

open AxiomaticGW.BlowupTwoLineH

def main : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn "index\tweighted\trunning_sum"
  let mut total : ℚ := 0
  for j in List.finRange 815 do
    let w := weighted j
    total := total + w
    stdout.putStrLn s!"{j.val}\t{w}\t{total}"
    stdout.flush
