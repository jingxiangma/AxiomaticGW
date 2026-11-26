/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHRow

/-!
# Boundary and shift consumers of the solved hyperplane row

The positive-energy exceptional boundary, arbitrary ancestor callbacks and
two genuinely different exceptional shifts exercise the solved H interface.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHRow
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupHPivots
open SurfaceGenusTwoBlowupHRow

/-- The minus-one pivot gives the positive remainder, even on the pure
exceptional class where a plane-degree denominator would vanish. -/
theorem pure_exceptional_value_has_correct_sign (values : Variable .hirzebruchOne → ℚ)
    (he : RationalTerms.eval values (row .hirzebruchOne 0 ![1, 0]) = 0) :
    values (hColumn .hirzebruchOne ![1, 0]) =
      RationalTerms.eval values (remainder .hirzebruchOne 0 ![1, 0]) :=
  value_eq_step .hirzebruchOne 0 values ![1, 0] (by decide +kernel) he

/-- Changing an arbitrary ancestor value cannot affect the computed H step. -/
theorem step_ignores_ancestor_callback (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) (values : Variable X → ℚ)
    (q : SurfaceAncestorKey X) (z : ℚ) :
    step X i (Function.update values (Sum.inl q) z) beta = step X i values beta := by
  apply step_congr X i _ _ beta hbeta
  intro gamma family _
  rw [Function.update_of_ne (show (Sum.inr (family.query gamma) : Variable X) ≠ Sum.inl q from
    by intro he; cases he)]

/-- Both exceptional shifts yield the same H value for every full positive
class when the original equations hold. Their shifted source classes differ. -/
theorem two_exceptional_shifts_agree (beta : SurfaceTarget.blowupTwo.Curve)
    (hbeta : 0 < SurfaceTarget.blowupTwo.effective.energy beta)
    (values : Variable .blowupTwo → ℚ)
    (h0 : RationalTerms.eval values (row .blowupTwo 0 beta) = 0)
    (h1 : RationalTerms.eval values (row .blowupTwo 1 beta) = 0) :
    step .blowupTwo 0 values beta = step .blowupTwo 1 values beta :=
  step_eq_of_rows .blowupTwo 0 1 values beta hbeta h0 h1

end AxiomaticGWTest.SurfaceGenusTwoBlowupHRow
