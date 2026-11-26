/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalMarkedGraphBenchmark

/-! # Marked graph controls on the exceptional axes -/

public section
namespace AxiomaticGWTest.GKM.ExceptionalMarkedGraphSupport
open AxiomaticGW AxiomaticGW.GKM
open GKM.ExceptionalMarkedGraphSupport
open CurveReplay.TwoBlowups renaming tables → bl2
open SurfaceFrames.TwoBlowups renaming request → twoFrame

/-- On E₁ its own marked divisor has nonzero restriction at the source fixed point. -/
theorem own_divisor_nonzero :
    let q : SurfaceQuery .blowupTwo := ⟨2, ![1, 0, 0], [⟨.exceptional 0, 7⟩]⟩
    let g : MarkedSupport bl2 q := ⟨⟨2, 1, FixedGraphSupport.singleCover bl2 2 1 false,
      by rw [FixedGraphSupport.degree_singleCover]; decide +kernel⟩, fun _ ↦ 0⟩
    insertionFactor q twoFrame.restrictions g ≠ 0 := by
  dsimp only
  unfold insertionFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  have hj : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
  have h : j = ⟨0, by decide⟩ := Fin.ext hj
  subst j
  exact EquivariantCoefficients.y_ne_zero

/-- A foreign divisor at the second mark kills the entire sum, including arbitrary class factors. -/
theorem foreign_sum {ι W : Type*} [Fintype ι] [AddCommMonoid W]
    [Module EquivariantCoefficients.Coefficient W] :
    let q : SurfaceQuery .blowupTwo := ⟨5, ![0, 3, 0], [⟨.unit, 4⟩, ⟨.exceptional 0, 7⟩]⟩
    ∀ (g : ι → MarkedSupport bl2 q) (weights : ι → W),
      ∑ j, insertionFactor q twoFrame.restrictions (g j) • weights j = 0 := by
  intro q g weights
  exact (foreign_divisor 1 0 (by decide) 3 q (by decide +kernel)
    (by decide +kernel)).class_sum_zero g weights

end AxiomaticGWTest.GKM.ExceptionalMarkedGraphSupport
