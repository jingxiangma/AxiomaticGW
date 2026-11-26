/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalRelations
public import AxiomaticGW.Surfaces.GenusTwoBlowupHOtherFamilies

/-!
# A solved hyperplane row with strictly earlier canonical dependencies

The existing complete shifted L24 row has H coefficient minus one at every
positive-energy full effective class. After collecting cancellations and
removing that exact column, every remaining nonconstant term is a canonical
query strictly earlier in the established plane-degree/family/energy order.

The H value is therefore the unchanged remainder. The shift may use either
exceptional divisor: if a valuation satisfies both original equations, both
steps agree. Geometric row validity and the remaining reconstruction families
are not supplied by this algebraic consequence.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHRow
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupHPivots
variable (X : SurfaceTarget)

-- The complete L24 expression uses the existing 815-column source dispatch.
set_option maxRecDepth 20000

/-- Collect cancellations in the existing full shifted row before removing
only its requested H column. Every constant and other coefficient remains. -/
def remainder (i : Fin X.blowups) (beta : X.Curve) : RationalTerms (Variable X) :=
  (RationalTerms.collect (row X i beta)).filter (fun t ↦ t.2 ≠ {hColumn X beta})

/-- The scalar step determined by the actual minus-one hyperplane pivot. -/
def step (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve) : ℚ :=
  RationalTerms.eval values (remainder X i beta)

/-- Every nonconstant collected remainder term is an actual canonical query
strictly earlier than the requested H variable. -/
theorem remainder_support (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ remainder X i beta) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ family : Family X,
      t.2 = {Sum.inr (family.query gamma)} ∧
        Earlier X (gamma, family) (beta, .hyperplane) := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  rcases L24Relation.collected_normalized_primary_canonical_support
    (pointCount X beta) (sourceCurve X i beta) _ ht with hz | ⟨gamma, c, hc, hm, _⟩
  · exact Or.inl hz
  · have ha := RationalTerms.mem_collect.mp ht
    have hcoef : RationalTerms.coefficient (row X i beta) {Sum.inr c} ≠ 0 := by
      rw [← hm, ← ha.2.1]
      exact ha.2.2
    obtain ⟨family, hf⟩ := family_of_mem_canonicalQueries hc
    rw [← hf] at hm hcoef
    have hs := SurfaceGenusTwoBlowupHOtherFamilies.canonical_coefficient_support
      X i beta gamma family hbeta hcoef
    refine Or.inr ⟨gamma, family, hm, ?_⟩
    rcases hs with ⟨rfl, rfl⟩ | hs
    · exact (hne hm).elim
    · exact hs

/-- The original complete shifted row splits into its minus-one pivot and
its unchanged collected remainder. -/
theorem eval_row (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.eval values (row X i beta) =
      -1 * values (hColumn X beta) + RationalTerms.eval values (remainder X i beta) := by
  rw [← RationalTerms.eval_collect values (row X i beta),
    RationalTerms.eval_isolate_singleton values _ (hColumn X beta),
    RationalTerms.coefficient_collect,
    SurfaceGenusTwoBlowupHContributions.row_coefficient_eq_neg_one X i beta hbeta,
    Algebra.algebraMap_self_apply]
  rfl

/-- A valuation satisfying the original shifted equation has the computed H
value, including at zero plane degree and arbitrary signed multiplicities. -/
theorem value_eq_step (i : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (he : RationalTerms.eval values (row X i beta) = 0) :
    values (hColumn X beta) = step X i values beta := by
  have heq := eval_row X i values beta hbeta
  rw [he] at heq
  change values (hColumn X beta) = RationalTerms.eval values (remainder X i beta)
  linarith

/-- Only strictly earlier canonical values can affect the computed H step. -/
theorem step_congr (i : Fin X.blowups) (values other : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .hyperplane) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    step X i values beta = step X i other beta := by
  apply RationalTerms.eval_congr
  intro t ht v hv
  rcases remainder_support X i beta hbeta ht with hz | ⟨gamma, family, hm, he⟩
  · exact (Multiset.notMem_zero v (hz ▸ hv)).elim
  · rw [hm, Multiset.mem_singleton] at hv
    subst v
    exact h gamma family he

/-- The original row uniquely determines H once earlier canonical values are fixed. -/
theorem value_unique (i : Fin X.blowups) (values other : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (he : RationalTerms.eval values (row X i beta) = 0)
    (ho : RationalTerms.eval other (row X i beta) = 0)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .hyperplane) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    values (hColumn X beta) = other (hColumn X beta) := by
  rw [value_eq_step X i values beta hbeta he, value_eq_step X i other beta hbeta ho]
  exact step_congr X i values other beta hbeta h

/-- Different exceptional shifts give the same H step when the valuation
satisfies both original equations; no equality of the source classes is imposed. -/
theorem step_eq_of_rows (i j : Fin X.blowups) (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (hi : RationalTerms.eval values (row X i beta) = 0)
    (hj : RationalTerms.eval values (row X j beta) = 0) :
    step X i values beta = step X j values beta := by
  rw [← value_eq_step X i values beta hbeta hi, ← value_eq_step X j values beta hbeta hj]

end AxiomaticGW.SurfaceGenusTwoBlowupHRow
