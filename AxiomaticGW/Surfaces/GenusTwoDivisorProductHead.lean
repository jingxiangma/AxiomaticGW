/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPrimitiveDivisorDescendants
public import AxiomaticGW.Surfaces.GenusTwoTwoMarkingProduct
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingKey

/-! # The genus-two rational-tail graph of the two-divisor product

In anticanonical degree one the rational component has class zero or the entire
input class. The two cases leave the positive-class point first ancestor and
degree-zero divisor first ancestors, respectively.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open GenusTwoPsiProduct SurfaceFirstDescendant
variable {X : SurfaceTarget}

/-- The weighted rational-tail graph before substituting its genus-two keys. -/
def productHead (beta : X.Curve) (a b : SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.scale (boundary (boundaryIndex 0))
    ((boundaryTerm 0).1.surfaceDecoratedTerms X (vertexTerms X)
      (boundaryTerm 0).2 beta 0 ![a, b])

theorem eval_productHead (base : SurfaceAncestorKey X → ℚ)
    (beta : X.Curve) (a b : SurfaceBasisLabel X) :
    RationalTerms.eval base (productHead beta a b) =
      productGraph (productVertex base) beta ![a, b] 0 := by
  simp only [productHead, productGraph, RationalTerms.eval_scale, Algebra.algebraMap_self_apply,
    GluingExpression.eval_surfaceDecoratedTerms]
  rfl

/-- The effective-class split and the inverse-metric signs of the remaining graph. -/
def divisorHeadTerms (beta : X.Curve) (a b : SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  RationalTerms.term (3 * divisorIntersection a b) {oneMarkingKey beta .point 1} +
  ∑ c : SurfaceBasisLabel X, if c.codimension = 1 then
      RationalTerms.term (3 * a.primaryFactor beta * b.primaryFactor beta *
        c.primaryFactor beta * c.inverseWeight) {oneMarkingKey 0 c 1}
    else 0

set_option maxRecDepth 65536

/-- All degree-one effective decompositions give exactly the stated sparse polynomial. -/
theorem productHead_eq (beta : X.Curve) (he : X.effective.energy beta = 1)
    (a b : SurfaceBasisLabel X) (ha : a.codimension = 1) (hb : b.codimension = 1) :
    productHead beta a b = divisorHeadTerms beta a b := by
  have h : ∀ beta ∈ X.bounded 1, X.effective.energy beta = 1 →
      ∀ a b : SurfaceBasisLabel X, a.codimension = 1 → b.codimension = 1 →
        productHead beta a b = divisorHeadTerms beta a b := by
    cases X <;> decide +kernel
  exact h beta (by rw [X.bounded_eq, X.effective.mem_bounded, he]) he a b ha hb

open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction

private theorem positive_point (i : Fin X.blowups) (beta : X.Curve)
    (he : X.effective.energy beta = 1) :
    SurfaceGenusTwoBlowupLowPsi.ancestorValue i (oneMarkingKey beta .point 1) =
      SurfaceGenusTwoBlowupRecursion.values i (beta, .point) := by
  have hh : ∀ b ∈ X.bounded 1, X.effective.energy b = 1 →
      normalizedTerms (oneMarkingKey b .point 1) =
        RationalTerms.term 1 {Sum.inr (Family.point.query b)} := by
    cases X <;> decide +kernel
  simp only [SurfaceGenusTwoBlowupLowPsi.ancestorValue,
    SurfaceGenusTwoBlowupLowPsi.ancestorValueWith,
    hh beta (by rw [X.bounded_eq, X.effective.mem_bounded, he]) he, RationalTerms.eval_term,
    Algebra.algebraMap_self_apply, Multiset.map_singleton, Multiset.prod_singleton,
    canonicalValuation_query, one_mul]

private def zeroLow (c : SurfaceBasisLabel X) : ℚ :=
  SurfaceGenusTwoBlowupLowPsi.ancestorValueWith
    (fun s ↦ SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
    (oneMarkingKey 0 c 1)

private theorem zeroLow_eq (i : Fin X.blowups) (c : SurfaceBasisLabel X) :
    SurfaceGenusTwoBlowupLowPsi.ancestorValue i (oneMarkingKey 0 c 1) = zeroLow c := by
  apply SurfaceGenusTwoBlowupLowPsi.ancestorValueWith_congr _ _ _ rfl (by change 1 ≤ 1; decide)
  intro b ⟨d, h⟩ f
  change b + d = 0 at h
  have he := congrArg X.effective.energy h
  rw [map_add, map_zero] at he
  have hb := (X.effective.energy_eq_zero_iff b).mp (by omega)
  exact SurfaceGenusTwoBlowupRecursion.values_boundary i (b, f) (by
    change X.planeDegree b = 0
    rw [hb, map_zero])

private def zeroContribution (beta : X.Curve) (a b : SurfaceBasisLabel X) : ℚ :=
  ∑ c : SurfaceBasisLabel X, if c.codimension = 1 then
    3 * a.primaryFactor beta * b.primaryFactor beta * c.primaryFactor beta * c.inverseWeight *
      zeroLow c
    else 0

/-- The classical rational three-point term reads P at the full class. The positive rational
three-point term reads only degree-zero first ancestors, with its original inverse-metric signs. -/
theorem divisorProductHead_value (i : Fin X.blowups) (beta : X.Curve)
    (he : X.effective.energy beta = 1) (a b : SurfaceBasisLabel X)
    (ha : a.codimension = 1) (hb : b.codimension = 1) :
    productGraph (productVertex (SurfaceGenusTwoBlowupLowPsi.ancestorValue i)) beta ![a,b] 0 =
      3 * divisorIntersection a b * SurfaceGenusTwoBlowupRecursion.values i (beta, .point) +
      (-1/960) * (a.primaryFactor beta * b.primaryFactor beta) := by
  have hz : ∀ t ∈ X.bounded 1, X.effective.energy t = 1 →
      ∀ u v : SurfaceBasisLabel X, u.codimension = 1 → v.codimension = 1 →
        zeroContribution t u v = (-1/960) * (u.primaryFactor t * v.primaryFactor t) := by
    cases X <;> decide +kernel
  rw [← eval_productHead, productHead_eq beta he a b ha hb, divisorHeadTerms,
    RationalTerms.eval_add, RationalTerms.eval_term, RationalTerms.eval_sum,
    Multiset.map_singleton, Multiset.prod_singleton,
    Algebra.algebraMap_self_apply, positive_point i beta he,
    ← hz beta (by rw [X.bounded_eq, X.effective.mem_bounded, he]) he a b ha hb]
  apply congrArg (fun x : ℚ ↦ 3 * divisorIntersection a b *
    SurfaceGenusTwoBlowupRecursion.values i (beta, .point) + x)
  unfold zeroContribution
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c.codimension = 1
  · simp only [if_pos hc, RationalTerms.eval_term, Algebra.algebraMap_self_apply,
      Multiset.map_singleton, Multiset.prod_singleton, zeroLow_eq i]
  · simp only [if_neg hc, RationalTerms.eval_zero]

end AxiomaticGW.SurfaceGenusTwo
