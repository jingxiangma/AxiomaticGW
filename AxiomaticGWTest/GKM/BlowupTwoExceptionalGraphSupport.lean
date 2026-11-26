/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoExceptionalGraphSupport

/-! # Positive controls for the mixed exceptional graph obstruction -/

@[expose] public section
namespace AxiomaticGWTest.GKM.BlowupTwoExceptionalGraphSupport
open AxiomaticGW AxiomaticGW.GKM
open CurveReplay.TwoBlowups (tables)
open FixedGraphSupport (singleCover degree_singleCover)

/-- Either orientation of a multiple cover realizes the full corresponding exceptional class. -/
theorem pure_covers (d : ℕ+) (reverse : Bool) :
    (singleCover tables 2 d reverse).degree = ![(d : ℕ), 0, 0] ∧
    (singleCover tables 4 d reverse).degree = ![0, (d : ℕ), 0] := by
  rw [degree_singleCover, degree_singleCover]
  constructor <;> funext k <;> fin_cases k <;>
    change (d : ℕ) * _ = _ <;> simp [tables, Matrix.cons_val_two]

/-- Connected fixed chain meeting both exceptional curves through their common transversal L. -/
def throughLine : FixedGraphSupport tables 4 3 where
  endpoint := ![![0, 1], ![1, 2], ![2, 3]]
  image := ![1, 2, 3, 4]
  edgeIndex := ![2, 3, 4]
  cover _ := 1
  incident := by decide +kernel
  connected := by decide +kernel

/-- Adding one copy of L removes the disjoint-support obstruction. -/
theorem throughLine_degree : throughLine.degree = ![1, 1, 1] := by decide +kernel

end AxiomaticGWTest.GKM.BlowupTwoExceptionalGraphSupport
