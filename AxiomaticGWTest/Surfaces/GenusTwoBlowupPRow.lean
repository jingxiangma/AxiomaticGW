/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPRow

/-!
# Consumers of the solved P row

The fiber equation tests the division sign, arbitrary ancestor callback
changes test actual closure, mixed classes retain all effective coordinates,
and zero plane degree remains outside the nonzero-pivot conclusion.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupPRow
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupPRow

/-- The fiber's negative eighteen pivot gives a positive remainder divided by
 eighteen, conditional on the original full equation. -/
theorem fiber_value_has_correct_sign (values : Variable .hirzebruchOne → ℚ)
    (he : RationalTerms.eval values (row .hirzebruchOne ![0, 1]) = 0) :
    values (Sum.inr (Family.point.query ![0, 1])) =
      RationalTerms.eval values (remainder .hirzebruchOne ![0, 1]) / 18 := by
  have h := value_eq_step .hirzebruchOne values ![0, 1]
    (by decide +kernel) (by decide +kernel) he
  simpa only [step, show SurfaceTarget.hirzebruchOne.planeDegree ![0, 1] = 1 from rfl,
    Nat.cast_one, mul_one] using h

/-- Changing any higher-ancestor callback cannot change the P step, because
its complete collected remainder uses only earlier canonical descendants. -/
theorem step_ignores_ancestor_callback (X : SurfaceTarget) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (values : Variable X → ℚ)
    (q : SurfaceAncestorKey X) (z : ℚ) :
    step X (Function.update values (Sum.inl q) z) beta = step X values beta := by
  apply step_congr X _ _ beta hbeta
  intro gamma family _
  rw [Function.update_of_ne (show (Sum.inr (family.query gamma) : Variable X) ≠ Sum.inl q from
    by intro he; cases he)]

-- This name-only linter unfolds the concrete membership proposition and executes
-- the full row. The binders below are not constructor names; kernel checking remains.
set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
/-- The mixed-class remainder keeps every actual variable's family and full
class, with strict order decrease rather than an energy-only substitute. -/
theorem mixed_full_class_dependencies {t : ℚ × Multiset (Variable .blowupTwo)}
    (ht : t ∈ remainder .blowupTwo ![4, 2, 1]) :
    t.2 = 0 ∨ ∃ gamma : SurfaceTarget.blowupTwo.Curve,
      ∃ family : Family .blowupTwo, t.2 = {Sum.inr (family.query gamma)} ∧
        Earlier .blowupTwo (gamma, family) (![4, 2, 1], .point) := by
  generalize hbeta : (![4, 2, 1] : SurfaceTarget.blowupTwo.Curve) = beta at *
  apply remainder_support .blowupTwo beta _ ht
  rw [← hbeta]
  decide +kernel

/-- The exceptional generator is positive energy but has zero P pivot.
The solved-row theorem's positive-plane-degree hypothesis is necessary. -/
theorem exceptional_pivot_is_zero :
    0 < SurfaceTarget.hirzebruchOne.effective.energy ![1, 0] ∧
      RationalTerms.coefficient (row .hirzebruchOne ![1, 0])
        {Sum.inr (Family.point.query ![1, 0])} = 0 := by
  refine ⟨by decide +kernel, ?_⟩
  have hp := SurfaceGenusTwoBlowupPCoefficients.point_coefficient
    (X := .hirzebruchOne) ![1, 0] (by decide +kernel)
  change RationalTerms.coefficient (row .hirzebruchOne ![1, 0])
    {Sum.inr (Family.point.query ![1, 0])} = _ at hp
  rw [hp, show SurfaceTarget.hirzebruchOne.planeDegree ![1, 0] = 0 from rfl,
    Nat.cast_zero, mul_zero]

end AxiomaticGWTest.SurfaceGenusTwoBlowupPRow
