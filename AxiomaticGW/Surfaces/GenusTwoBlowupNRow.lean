/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNCanonicalSupport

/-!
# The scalar step of the four-relation primary genus-two equation

The original combined BP row has primary coefficient `6d`. Collection retains
all constants and cancels repeated columns before isolating only `N_beta`.
At positive plane degree the original equation determines this value as the
negative remainder divided by `6d`. No numerical recurrence is assumed.

The complete canonical support theorem makes every remaining nonconstant
column strictly earlier in the established order. This step is uniquely
determined by earlier values; finite-seed reconstruction is assembled separately.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupNRow
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupNRelation
variable (X : SurfaceTarget)

/-- Collect all cancellations before removing the requested primary column alone. -/
def remainder (i : Fin X.blowups) (beta : X.Curve) : RationalTerms (Variable X) :=
  (RationalTerms.collect (row X i beta)).filter
    (fun t ↦ t.2 ≠ {Sum.inr (Family.primary.query beta)})

/-- The original equation determines the negative remainder over its positive `6d` pivot. -/
def step (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve) : ℚ :=
  -RationalTerms.eval values (remainder X i beta) / (6 * (X.planeDegree beta : ℚ))

/-- Every remaining nonconstant column is a strictly earlier canonical query. -/
theorem remainder_support (i : Fin X.blowups) (beta : X.Curve)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ remainder X i beta) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ family : Family X,
      t.2 = {Sum.inr (family.query gamma)} ∧ Earlier X (gamma, family) (beta, .primary) := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  rcases collected_row_canonical_support i beta ht with hz | ⟨gamma, c, hc, hm, _⟩
  · exact Or.inl hz
  · have ha := RationalTerms.mem_collect.mp ht
    have hcoef : RationalTerms.coefficient (row X i beta) {Sum.inr c} ≠ 0 := by
      rw [← hm, ← ha.2.1]
      exact ha.2.2
    obtain ⟨family, hf⟩ := family_of_mem_canonicalQueries hc
    rw [← hf] at hm hcoef
    have hs := SurfaceGenusTwoBlowupNCanonicalSupport.canonical_coefficient_support
      i beta gamma family hcoef
    refine Or.inr ⟨gamma, family, hm, ?_⟩
    rcases hs with ⟨rfl, rfl⟩ | hs
    · exact (hne hm).elim
    · exact hs

/-- Isolate the exact primary pivot, preserving every other coefficient and the constant. -/
theorem eval_row (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve) :
    RationalTerms.eval values (row X i beta) =
      (6 * (X.planeDegree beta : ℚ)) * values (Sum.inr (Family.primary.query beta)) +
        RationalTerms.eval values (remainder X i beta) := by
  rw [← RationalTerms.eval_collect values (row X i beta),
    RationalTerms.eval_isolate_singleton values _ (Sum.inr (Family.primary.query beta)),
    RationalTerms.coefficient_collect]
  have hp := SurfaceGenusTwoBlowupNCoefficients.row_primary_coefficient i beta
  change RationalTerms.coefficient (row X i beta) {Sum.inr (Family.primary.query beta)} = _ at hp
  rw [hp, Algebra.algebraMap_self_apply]
  rfl

/-- The complete unsolved equation determines the primary value whenever its pivot is nonzero. -/
theorem value_eq_step (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hd : 0 < X.planeDegree beta) (he : RationalTerms.eval values (row X i beta) = 0) :
    values (Sum.inr (Family.primary.query beta)) = step X i values beta := by
  have heq := eval_row X i values beta
  rw [he] at heq
  have hden : (6 * (X.planeDegree beta : ℚ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
  apply (eq_div_iff hden).mpr
  change values (Sum.inr (Family.primary.query beta)) *
      (6 * (X.planeDegree beta : ℚ)) = -RationalTerms.eval values (remainder X i beta)
  linarith

/-- Only strictly earlier canonical values affect the primary step. -/
theorem step_congr (i : Fin X.blowups) (values other : Variable X → ℚ) (beta : X.Curve)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .primary) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    step X i values beta = step X i other beta := by
  apply congrArg (fun r : ℚ ↦ -r / (6 * (X.planeDegree beta : ℚ)))
  apply RationalTerms.eval_congr
  intro t ht v hv
  rcases remainder_support X i beta ht with hz | ⟨gamma, family, hm, he⟩
  · exact (Multiset.notMem_zero v (hz ▸ hv)).elim
  · rw [hm, Multiset.mem_singleton] at hv
    subst v
    exact h gamma family he

/-- The original combined equation uniquely determines its primary value from earlier values. -/
theorem value_unique (i : Fin X.blowups) (values other : Variable X → ℚ) (beta : X.Curve)
    (hd : 0 < X.planeDegree beta)
    (he : RationalTerms.eval values (row X i beta) = 0)
    (ho : RationalTerms.eval other (row X i beta) = 0)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .primary) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    values (Sum.inr (Family.primary.query beta)) = other (Sum.inr (Family.primary.query beta)) := by
  rw [value_eq_step X i values beta hd he, value_eq_step X i other beta hd ho]
  exact step_congr X i values other beta h

/-- Either exceptional shift computes the same primary value when its original equation holds. -/
theorem step_eq_of_rows (i j : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hd : 0 < X.planeDegree beta)
    (hi : RationalTerms.eval values (row X i beta) = 0)
    (hj : RationalTerms.eval values (row X j beta) = 0) :
    step X i values beta = step X j values beta := by
  rw [← value_eq_step X i values beta hd hi, ← value_eq_step X j values beta hd hj]

end AxiomaticGW.SurfaceGenusTwoBlowupNRow
