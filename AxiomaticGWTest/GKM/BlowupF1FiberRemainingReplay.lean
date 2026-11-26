/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupF1FiberRemainingReplay

/-! # Fiber P, N and K regression at the exact incoming descendant states -/

@[expose] public section
namespace AxiomaticGWTest.GKM.BlowupF1FiberRemainingReplay
open AxiomaticGW SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction
open AxiomaticGW.GKM.BlowupF1FiberRemainingReplay

/-- Each stable, dimension-compatible request maps back to its intended full canonical
state and its incoming ordinary value agrees with the reconstructed value. -/
theorem exact_queries (i : Fin 3) :
    (requests i).DimensionCompatible ∧ (requests i).GeometricDomain ∧
      state? (requests i) = some (![0, 1], (families i)) ∧
      canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests i)) =
        values i := by
  refine ⟨?_, ?_, ?_, accepted i⟩
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · rw [coverage, state?_query]

end AxiomaticGWTest.GKM.BlowupF1FiberRemainingReplay
