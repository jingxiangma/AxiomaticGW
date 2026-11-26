/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1PlaneLineCanonical
public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineL24Replay

/-! # Independent canonical comparisons for the pullback line on F₁

Every ordered incoming genus-two localization request is bound to the same
full-class query in the original reconstructed canonical valuation.
-/

@[expose] public section
namespace AxiomaticGW.GKM.F1PlaneLine
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction

/-- All four incoming ordinary specializations agree with the reconstructed H, P, N and K. -/
theorem accepted (j : Fin 4) :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests j)) =
      values j := by
  rw [coverage, canonicalValuation_query]
  trans 0
  · exact AxiomaticGW.F1PlaneLine.line_values _
  · fin_cases j <;> decide +kernel

end AxiomaticGW.GKM.F1PlaneLine
