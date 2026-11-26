/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoExceptionalInitialValues

/-!
# Regression coefficients for F₁'s derived initial value

These valuations test the complete normalized BP equation and do not claim
to be geometric invariant models. They retain the degree-zero seed's exact
normalization, the primary pivot and both signed exceptional descendants.
-/

@[expose] public section

open AxiomaticGW AxiomaticGW.SurfaceGenusTwo AxiomaticGW.BelorousskiPandharipande

namespace AxiomaticGWTest.GenusTwoExceptionalInitialValues

/-- Artificial component values for coefficient regressions, without a geometric model. -/
def exceptionalValuation (n k₀ k p : ℚ) :
    SurfacePolynomialReduction.Variable .hirzebruchOne → ℚ := fun v ↦
  if v = Sum.inr (SurfaceQuery.points .hirzebruchOne 2 0 1) then n
  else if v = Sum.inr (SurfaceFirstDescendant.query 2 0 (.exceptional 0) 0) then k₀
  else if v = Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] (.exceptional 0) 1) then k
  else if v = Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] .point 0) then p
  else 0

/-- The audited exceptional seed cancels the full equation's constant. -/
theorem auditedExceptionalSeedCancels : RationalTerms.eval (exceptionalValuation 0 (-1 / 2880) 0 0)
    (normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0 (fun _ ↦ .exceptional 0)) = 0 := by
  rw [hirzebruchOne_exceptional_equation]
  decide +kernel

/-- Substituting the hyperplane normalization for the exceptional seed leaves a residual. -/
theorem hyperplaneSeedResidual : RationalTerms.eval (exceptionalValuation 0 (-1 / 960) 0 0)
    (normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0 (fun _ ↦ .exceptional 0)) = 1 / 120 := by
  rw [hirzebruchOne_exceptional_equation]
  decide +kernel

/-- The class-zero primary survives with its nonzero pivot. -/
theorem primaryPivot : RationalTerms.eval (exceptionalValuation 1 (-1 / 2880) 0 0)
    (normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0 (fun _ ↦ .exceptional 0)) = 12 := by
  rw [hirzebruchOne_exceptional_equation]
  decide +kernel

/-- Both exceptional descendants retain the signs produced by rational-tail comparison. -/
theorem signedExceptionalDescendants : RationalTerms.eval (exceptionalValuation 0 (-1 / 2880) 1 2)
    (normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0 (fun _ ↦ .exceptional 0)) = -54 := by
  rw [hirzebruchOne_exceptional_equation]
  decide +kernel

end AxiomaticGWTest.GenusTwoExceptionalInitialValues
