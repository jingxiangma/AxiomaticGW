/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineCanonicalReplay

/-! # The five complete incoming canonical queries on the two-point strict line -/

@[expose] public section
namespace AxiomaticGWTest.GKM.BlowupTwoLineCanonical
open AxiomaticGW SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction
open AxiomaticGW.GKM.BlowupTwoLineCanonical

/-- Dimension, stability and the exact inverse query lookup hold for every incoming row. -/
theorem exact_queries (i : Fin 5) :
    (requests i).DimensionCompatible ∧ (requests i).GeometricDomain ∧
      state? (requests i) = some (![0, 0, 1], families i) ∧
      canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests i)) =
        values i := by
  refine ⟨?_, ?_, ?_, accepted i⟩
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · rw [coverage, state?_query]

end AxiomaticGWTest.GKM.BlowupTwoLineCanonical
