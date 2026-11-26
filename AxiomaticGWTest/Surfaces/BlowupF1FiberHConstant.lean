/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHConstant

/-! The integrated row keeps its target F separate from its shifted source E+F. -/

@[expose] public section

namespace AxiomaticGWTest.BlowupF1FiberHConstant
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupScalar

/-- Substituting the shifted source for the target would change a nonzero pivot to zero. -/
theorem target_and_source_columns_differ :
    singletonCoefficient (X := .hirzebruchOne) 0 (![0, 1], .hyperplane)
        (.inr (Family.hyperplane.query ![0, 1])) = -1 ∧
      singletonCoefficient (X := .hirzebruchOne) 0 (![0, 1], .hyperplane)
        (.inr (Family.hyperplane.query ![1, 1])) = 0 := by
  refine ⟨AxiomaticGW.BlowupF1FiberHConstant.singleton_coefficient, ?_⟩
  rw [singletonCoefficient_eq]
  have h := SurfaceGenusTwoBlowupHSupport.source_column_row_coefficient_eq_zero
    .hirzebruchOne 0 ![0, 1] (by decide +kernel)
  have hs : SurfaceGenusTwoBlowupHPivots.sourceCurve .hirzebruchOne 0 ![0, 1] =
      ![1, 1] := by decide +kernel
  rw [hs] at h
  exact h

end AxiomaticGWTest.BlowupF1FiberHConstant
