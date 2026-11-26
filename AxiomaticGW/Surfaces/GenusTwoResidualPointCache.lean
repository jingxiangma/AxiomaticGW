/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoL24PointCache
public import AxiomaticGW.Surfaces.GenusTwoCachedComponents

/-!
# Materializing existing residual caches with proved-equal point backends

This module uses the existing `ResidualCache` and its exact `values_eq`
specification. Selected dimension-compatible lower-genus entries are computed
with the proved-equal primary-backed recursion. Other entries retain the
original residual expression. Cache misses also use that proved-equal
recursion; no selection-coverage condition or numerical seed is added.

The constant vertex retains its original guards. Point pullbacks, full curve
splits, signed contractions, and the complete L24 sum are unchanged.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Construct the original residual expression without first evaluating the
old point algorithm on dimension-compatible lower-genus components. -/
def residualTermsWithPoints (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) : RationalTerms (SurfaceAncestorKey X) :=
  if q.DimensionCompatible ∧ q.genus ≤ 1 then
    RationalTerms.term (SurfaceLowGenusPointCache.componentValue X v₀ v₁ q) 0
  else residualTerms q

/-- Both scalar and residual-variable sectors keep their original expressions. -/
theorem residualTermsWithPoints_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (q : SurfaceAncestorKey X) :
    residualTermsWithPoints X v₀ v₁ q = residualTerms q := by
  unfold residualTermsWithPoints
  split_ifs with h
  · rw [residualTerms, if_pos h.1, if_pos h.2,
      SurfaceLowGenusPointCache.componentValue_eq X v₀ v₁ h₀ h₁]
  · rfl

/-- Materialize the existing cache using the proved-equal point functions.
The proof field certifies the original residual expression at every selected key. -/
def ResidualCache.ofQueriesWithPoints (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (queries : Finset (SurfaceAncestorKey X)) : ResidualCache X where
  queries := queries
  values := queries.val.map (fun q ↦ (q, residualTermsWithPoints X v₀ v₁ q))
  values_eq := by
    simp only [residualTermsWithPoints_eq X v₀ v₁ h₀ h₁]

/-- Use the existing certified scalar lookup on a valid hit; compute all other
queries with the exact point-backed ancestor algorithm. -/
def cachedLowerValueWithPoints (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  if q.DimensionCompatible ∧ q.genus ≤ 1 ∧ q ∈ cache.queries then
    cachedLowerValue cache q
  else SurfaceLowGenusPointCache.componentValue X v₀ v₁ q

/-- Missing keys do not invoke the original uncached point recursion. -/
theorem cachedLowerValueWithPoints_of_missing (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X) (hq : q ∉ cache.queries) :
    cachedLowerValueWithPoints X cache v₀ v₁ q =
      SurfaceLowGenusPointCache.componentValue X v₀ v₁ q :=
  if_neg (fun h ↦ hq h.2.2)

/-- A certified lower-genus hit uses the existing cache API unchanged. -/
theorem cachedLowerValueWithPoints_of_present (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X)
    (hd : q.DimensionCompatible) (hg : q.genus ≤ 1) (hq : q ∈ cache.queries) :
    cachedLowerValueWithPoints X cache v₀ v₁ q = cachedLowerValue cache q :=
  if_pos ⟨hd, hg, hq⟩

/-- The wrapper preserves the existing scalar cache, including incomplete selections. -/
theorem cachedLowerValueWithPoints_eq_cached (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (h₀ : v₀ = SurfaceGenusZero.pointValue X)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) (q : SurfaceAncestorKey X) :
    cachedLowerValueWithPoints X cache v₀ v₁ q = cachedLowerValue cache q := by
  unfold cachedLowerValueWithPoints
  split_ifs
  · rfl
  · exact (congrFun (SurfaceLowGenusPointCache.componentValue_eq X v₀ v₁ h₀ h₁) q).trans
      (cachedLowerValue_eq cache q).symm

/-- No genus, dimension, or cache-membership premise restricts this equality. -/
theorem cachedLowerValueWithPoints_eq (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (h₀ : v₀ = SurfaceGenusZero.pointValue X)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) (q : SurfaceAncestorKey X) :
    cachedLowerValueWithPoints X cache v₀ v₁ q =
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q :=
  (cachedLowerValueWithPoints_eq_cached X cache v₀ v₁ h₀ h₁ q).trans
    (cachedLowerValue_eq cache q)

/-- Keep the original constant vertex guards while reusing certified component expressions. -/
def constantVertexWithPointCache (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    if g ≤ 1 then
      let q := SurfaceAncestorKey.ofLabels g S h beta k a
      if q.DimensionCompatible then cachedLowerValueWithPoints X cache v₀ v₁ q else 0
    else 0

/-- Every constant component agrees with the original zero valuation. -/
theorem constantVertexWithPointCache_eq (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (h₀ : v₀ = SurfaceGenusZero.pointValue X)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) :
    constantVertexWithPointCache X cache v₀ v₁ = constantVertex X := by
  funext g S inst h beta k a
  simp only [constantVertexWithPointCache, constantVertex,
    cachedLowerValueWithPoints_eq X cache v₀ v₁ h₀ h₁]

/-- The full scalar contraction reuses components, with the same higher-genus guard. -/
def guardedConstantPointContractionWithPointCache (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) {g : ℕ} {S : Type} [Fintype S]
    (z : GluingExpression.CotangentTerm g S) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) : ℚ :=
  if 2 ≤ z.expression.maxComponentGenus then 0 else
    z.expression.scalarPointContraction X
      (SurfacePointPullback.vertex X (constantVertexWithPointCache X cache v₀ v₁))
      z.decoration z.labels beta n a

/-- All graph, marking, metric, and full-class data are retained under cache reuse. -/
theorem guardedConstantPointContractionWithPointCache_eq (X : SurfaceTarget)
    (cache : ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    {g : ℕ} {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    guardedConstantPointContractionWithPointCache X cache v₀ v₁ z beta n a =
      guardedConstantPointContraction X z beta n a := by
  rw [guardedConstantPointContractionWithPointCache,
    constantVertexWithPointCache_eq X cache v₀ v₁ h₀ h₁]
  rfl

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.L24Relation

/-- The complete L24 sum with a materialized existing residual cache. -/
def pointConstantWithPointCache (X : SurfaceTarget) (cache : SurfaceGenusTwo.ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  (cotangentRelation.map fun t ↦ t.1 *
    SurfaceGenusTwo.guardedConstantPointContractionWithPointCache X cache v₀ v₁
      t.2 beta n a).sum

/-- Finite cache selection never alters the complete original weighted equation. -/
theorem pointConstantWithPointCache_eq_guarded (X : SurfaceTarget)
    (cache : SurfaceGenusTwo.ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPointCache X cache v₀ v₁ n beta a = pointConstantGuarded X n beta a := by
  simp only [pointConstantWithPointCache, pointConstantGuarded,
    SurfaceGenusTwo.guardedConstantPointContractionWithPointCache_eq X cache v₀ v₁ h₀ h₁]

/-- The original scalar constant is recovered without any query-coverage assumption. -/
theorem pointConstantWithPointCache_eq (X : SurfaceTarget)
    (cache : SurfaceGenusTwo.ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPointCache X cache v₀ v₁ n beta a = pointConstant X n beta a :=
  (pointConstantWithPointCache_eq_guarded X cache v₀ v₁ h₀ h₁ n beta a).trans
    (pointConstantGuarded_eq X n beta a)

/-- The same cache computes the exact constant of the complete normalized polynomial. -/
theorem pointConstantWithPointCache_eq_normalized (X : SurfaceTarget)
    (cache : SurfaceGenusTwo.ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPointCache X cache v₀ v₁ n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) :=
  (pointConstantWithPointCache_eq X cache v₀ v₁ h₀ h₁ n beta a).trans
    (pointConstant_eq_normalized X n beta a)

end AxiomaticGW.L24Relation
