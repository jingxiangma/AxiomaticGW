/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCanonicalRelations
public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimarySupport

/-!
# A solved P row with strictly earlier canonical dependencies

The complete normalized BP HHH equation has P coefficient minus eighteen
times plane degree. Collection removes cancelled dependencies before this
column is isolated. Every remaining nonconstant term is an actual canonical
query strictly earlier in the established plane-degree/family/energy order.

At positive plane degree, the row therefore determines its P value from
those earlier values and the original lower-genus constant. This module
proves the executable scalar step and its uniqueness relative to earlier
values. It does not supply the other canonical rows, geometric validity of
the input equation, a finite-seed reconstruction or the degree-zero sector.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupPRow
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable (X : SurfaceTarget)

/-- The original complete normalized HHH equation at its canonical point count. -/
def row (beta : X.Curve) : RationalTerms (Variable X) :=
  BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
    beta 0 (SurfaceGenusZero.pointLabels
      (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
      (X.effective.energy beta - 1))

/-- Collect all cancellations before removing only the requested P column.
Constants and every other original coefficient are retained. -/
def remainder (beta : X.Curve) : RationalTerms (Variable X) :=
  (RationalTerms.collect (row X beta)).filter
    (fun t ↦ t.2 ≠ {Sum.inr (Family.point.query beta)})

/-- The rational scalar step determined by the HHH row. Its use as a solved
row requires positive plane degree; no recursive values are supplied here. -/
def step (values : Variable X → ℚ) (beta : X.Curve) : ℚ :=
  RationalTerms.eval values (remainder X beta) / (18 * (X.planeDegree beta : ℚ))

/-- Every nonconstant collected remainder term is an actual canonical query
strictly earlier than the requested P variable in the proved order. -/
theorem remainder_support (beta : X.Curve) (hbeta : 0 < X.effective.energy beta)
    {t : ℚ × Multiset (Variable X)} (ht : t ∈ remainder X beta) :
    t.2 = 0 ∨ ∃ gamma : X.Curve, ∃ family : Family X,
      t.2 = {Sum.inr (family.query gamma)} ∧ Earlier X (gamma, family) (beta, .point) := by
  obtain ⟨ht, hne⟩ := Multiset.mem_filter.mp ht
  rcases BelorousskiPandharipande.collected_normalized_primary_canonical_support
    (X.effective.energy beta - 1) beta _ ht with hz | ⟨gamma, c, hc, hm, _⟩
  · exact Or.inl hz
  · have ha := RationalTerms.mem_collect.mp ht
    have hcoef : RationalTerms.coefficient (row X beta) {Sum.inr c} ≠ 0 := by
      rw [← hm, ← ha.2.1]
      exact ha.2.2
    obtain ⟨family, hf⟩ := family_of_mem_canonicalQueries hc
    rw [← hf] at hm hcoef
    have hs := SurfaceGenusTwoBlowupPPrimarySupport.canonical_coefficient_support
      beta gamma family hbeta hcoef
    refine Or.inr ⟨gamma, family, hm, ?_⟩
    rcases hs with ⟨rfl, rfl⟩ | hs
    · exact (hne hm).elim
    · exact hs

/-- The complete row splits into its proved P pivot and the unchanged
collected remainder, with the constant sign preserved. -/
theorem eval_row (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.eval values (row X beta) =
      (-18 * (X.planeDegree beta : ℚ)) * values (Sum.inr (Family.point.query beta)) +
        RationalTerms.eval values (remainder X beta) := by
  rw [← RationalTerms.eval_collect values (row X beta),
    RationalTerms.eval_isolate_singleton values _ (Sum.inr (Family.point.query beta)),
    RationalTerms.coefficient_collect]
  have hp := SurfaceGenusTwoBlowupPCoefficients.point_coefficient beta hbeta
  change RationalTerms.coefficient (row X beta) {Sum.inr (Family.point.query beta)} = _ at hp
  rw [hp, Algebra.algebraMap_self_apply]
  rfl

/-- Any valuation satisfying the original complete HHH equation has the
computed P value at positive plane degree. This is an algebraic consequence
of that equation, not an assumed reconstruction recurrence. -/
theorem value_eq_step (values : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (hd : 0 < X.planeDegree beta)
    (he : RationalTerms.eval values (row X beta) = 0) :
    values (Sum.inr (Family.point.query beta)) = step X values beta := by
  have heq := eval_row X values beta hbeta
  rw [he] at heq
  have hden : (18 * (X.planeDegree beta : ℚ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
  apply (eq_div_iff hden).mpr
  change values (Sum.inr (Family.point.query beta)) *
      (18 * (X.planeDegree beta : ℚ)) = RationalTerms.eval values (remainder X beta)
  linarith

/-- Only already earlier canonical values can affect the computed P step.
In particular no ancestor callback or hidden same-order value is needed. -/
theorem step_congr (values other : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .point) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    step X values beta = step X other beta := by
  apply congrArg (fun r : ℚ ↦ r / (18 * (X.planeDegree beta : ℚ)))
  apply RationalTerms.eval_congr
  intro t ht v hv
  rcases remainder_support X beta hbeta ht with hz | ⟨gamma, family, hm, he⟩
  · exact (Multiset.notMem_zero v (hz ▸ hv)).elim
  · rw [hm, Multiset.mem_singleton] at hv
    subst v
    exact h gamma family he

/-- The original row uniquely determines its P value once earlier canonical
values are fixed, provided its actual pivot is nonzero. -/
theorem value_unique (values other : Variable X → ℚ) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) (hd : 0 < X.planeDegree beta)
    (he : RationalTerms.eval values (row X beta) = 0)
    (ho : RationalTerms.eval other (row X beta) = 0)
    (h : ∀ gamma : X.Curve, ∀ family : Family X,
      Earlier X (gamma, family) (beta, .point) →
        values (Sum.inr (family.query gamma)) = other (Sum.inr (family.query gamma))) :
    values (Sum.inr (Family.point.query beta)) = other (Sum.inr (Family.point.query beta)) := by
  rw [value_eq_step X values beta hbeta hd he, value_eq_step X other beta hbeta hd ho]
  exact step_congr X values other beta hbeta h

end AxiomaticGW.SurfaceGenusTwoBlowupPRow
