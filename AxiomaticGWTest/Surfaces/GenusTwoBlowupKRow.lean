/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupKRow

/-!
# Boundary consumers of the solved exceptional row

Pure exceptional and zero-intersection classes still have a solved K row.
These consumers check its division sign and independence from all ancestor
callbacks while preserving the original complete BP equation as premise.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupKRow
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupKRow

/-- The pure exceptional class has plane degree zero but a valid K scalar step.
The negative pivot gives a positive remainder divided by eighteen. -/
theorem pure_exceptional_value_has_correct_sign (values : Variable .hirzebruchOne → ℚ)
    (he : RationalTerms.eval values (row .hirzebruchOne 0 ![1, 0]) = 0) :
    values (Sum.inr ((Family.exceptional 0).query ![1, 0])) =
      RationalTerms.eval values (remainder .hirzebruchOne 0 ![1, 0]) / 18 :=
  value_eq_step .hirzebruchOne 0 values ![1, 0] (by decide +kernel) he

/-- A zero exceptional intersection is not a singularity of the solved K row. -/
theorem zero_intersection_value (values : Variable .blowupTwo → ℚ)
    (he : RationalTerms.eval values (row .blowupTwo 0 ![1, 0, 1]) = 0) :
    SurfaceTarget.blowupTwo.signedMultiplicity ![1, 0, 1] 0 = 0 ∧
      values (Sum.inr ((Family.exceptional 0).query ![1, 0, 1])) =
        RationalTerms.eval values (remainder .blowupTwo 0 ![1, 0, 1]) / 18 := by
  exact ⟨by decide +kernel,
    value_eq_step .blowupTwo 0 values ![1, 0, 1] (by decide +kernel) he⟩

/-- No arbitrary ancestor input can affect the computed exceptional descendant. -/
theorem step_ignores_ancestor_callback (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) (values : Variable X → ℚ)
    (q : SurfaceAncestorKey X) (z : ℚ) :
    step X i (Function.update values (Sum.inl q) z) beta = step X i values beta := by
  apply step_congr X i _ _ beta hbeta
  intro gamma family _
  rw [Function.update_of_ne (show (Sum.inr (family.query gamma) : Variable X) ≠ Sum.inl q from
    by intro he; cases he)]

end AxiomaticGWTest.SurfaceGenusTwoBlowupKRow
