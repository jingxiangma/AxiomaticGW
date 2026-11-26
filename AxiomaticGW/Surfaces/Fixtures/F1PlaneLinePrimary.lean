/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineReduction
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-! # Shifted BP primary equation for the pullback line on the one-point blowup

The four original BP contractions occur at 2E+F with three added points. Each
lower-genus part retains its original weights, effective splittings and six
assignments of the distinguished divisors.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLine
open SurfaceGenusTwoBlowupScalar SurfacePointBenchmarkCache BelorousskiPandharipande

set_option Elab.async false
set_option maxRecDepth 20000

private def tripleLabels : Fin 4 → Fin 3 → SurfaceBasisLabel X :=
  ![![.exceptional 0, .hyperplane, .hyperplane], ![.exceptional 0, .exceptional 0, .hyperplane],
    ![.exceptional 0, .exceptional 0, .exceptional 0], ![.hyperplane, .hyperplane, .hyperplane]]

set_option maxHeartbeats 1000000 in
-- Six orderings and sixteen lower-genus graph types enter each original summand.
private theorem shifted_bp_constant (k : Fin 4) :
    lowerPointConstantWithPrimary X (genusZero X) (genusOne X) 3 ![2,1] (tripleLabels k) = 0 := by
  rw [lowerPointConstantWithPrimary_eq_primaryGraphSum]
  fin_cases k <;> decide +kernel

/-- The four terms, with the original coefficients 3/2, −1, 1/2 and −1/3, sum to zero. -/
theorem primary_constant : constant 0 (line, .primary) = 0 := by
  have he : X.effective.energy line = 3 := by decide +kernel
  have hs : line + X.exceptionalCurve 0 = ![2,1] := by decide +kernel
  have hd : X.planeDegree line = 1 := by decide +kernel
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (line, .primary) _ _
    (genusZero_eq X) (genusOne_eq X)]
  simp only [SurfaceGenusTwoBlowupPointCache.constant, he, hs, hd]
  have h₀ := shifted_bp_constant 0
  have h₁ := shifted_bp_constant 1
  have h₂ := shifted_bp_constant 2
  have h₃ := shifted_bp_constant 3
  change _ * lowerPointConstantWithPrimary X _ _ 3 _ (tripleLabels 0) +
    _ * lowerPointConstantWithPrimary X _ _ 3 _ (tripleLabels 1) +
    _ * lowerPointConstantWithPrimary X _ _ 3 _ (tripleLabels 2) +
    _ * lowerPointConstantWithPrimary X _ _ 3 _ (tripleLabels 3) = _
  rw [h₀, h₁, h₂, h₃]
  norm_num only

end AxiomaticGW.F1PlaneLine
