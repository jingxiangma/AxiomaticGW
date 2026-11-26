/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupF1FiberHReplay
public import AxiomaticGWTest.Surfaces.BlowupF1FiberHConstant

/-! The incoming value retains the full descendant key and the target/source distinction. -/

@[expose] public section

namespace AxiomaticGWTest.GKM.BlowupF1FiberHReplay
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupScalar
open AxiomaticGW.GKM.BlowupF1FiberHReplay

/-- The matched incoming value is at the dimension-compatible fiber request with pivot -1,
while the distinct shifted source column has coefficient zero. -/
theorem accepted_query_and_source_distinction :
    request = ⟨2, ![0, 1], [⟨.hyperplane, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩ ∧
      request.DimensionCompatible ∧
      state? request = some (![0, 1], .hyperplane) ∧
      canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr request) = value ∧
      singletonCoefficient (X := .hirzebruchOne) 0 (![0, 1], .hyperplane)
        (.inr (Family.hyperplane.query ![0, 1])) = -1 ∧
      singletonCoefficient (X := .hirzebruchOne) 0 (![0, 1], .hyperplane)
        (.inr (Family.hyperplane.query ![1, 1])) = 0 := by
  refine ⟨rfl, ?_, ?_, accepted, ?_⟩
  · rw [request_eq]
    exact AxiomaticGW.BlowupF1FiberHValue.query_dimensionCompatible
  · rw [request_eq]
    exact AxiomaticGW.BlowupF1FiberHValue.state_query
  · exact AxiomaticGWTest.BlowupF1FiberHConstant.target_and_source_columns_differ

end AxiomaticGWTest.GKM.BlowupF1FiberHReplay
