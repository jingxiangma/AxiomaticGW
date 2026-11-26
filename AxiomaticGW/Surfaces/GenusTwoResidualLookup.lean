/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoResidualPointCache
public import Mathlib.Data.Multiset.Find

/-!
# Early lookup in the existing certified residual cache

The existing `values_eq` field makes entries with the same full query key
subsingleton. Mathlib's exposed `Multiset.find?` therefore gives an exact,
computable first-match lookup on the stored multiset, without a second cache
format or a lossy key encoding. A hit avoids membership scans and the sum of
all other entries. A miss keeps the proved-equal point-backed recursion.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- The existing cache specification determines every stored full key and expression. -/
theorem ResidualCache.mem_values_iff (cache : ResidualCache X)
    (t : SurfaceAncestorKey X × RationalTerms (SurfaceAncestorKey X)) :
    t ∈ cache.values ↔ t.1 ∈ cache.queries ∧ t.2 = residualTerms t.1 := by
  rw [cache.values_eq]
  constructor
  · intro ht
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp ht
    exact ⟨hq, rfl⟩
  · rintro ⟨hq, ht⟩
    exact Multiset.mem_map.mpr ⟨t.1, hq, Prod.ext rfl ht.symm⟩

/-- Two matching stored entries are the same pair; no order is imposed on the cache. -/
theorem ResidualCache.matching_entries_subsingleton (cache : ResidualCache X)
    (q : SurfaceAncestorKey X) : {t ∈ cache.values | t.1 = q}.Subsingleton := by
  intro a ha b hb
  have hvalA := (cache.mem_values_iff a).mp ha.1
  have hvalB := (cache.mem_values_iff b).mp hb.1
  apply Prod.ext
  · exact ha.2.trans hb.2.symm
  · rw [hvalA.2, hvalB.2, ha.2, hb.2]

/-- Read the stored expression once at the first matching full query key. -/
def ResidualCache.lookup? (cache : ResidualCache X) (q : SurfaceAncestorKey X) :
    Option (RationalTerms (SurfaceAncestorKey X)) :=
  (cache.values.find? (fun t ↦ t.1 = q)
    (cache.matching_entries_subsingleton q)).map Prod.snd

/-- A hit contains exactly the original residual expression, including a zero expression. -/
theorem ResidualCache.lookup?_of_mem (cache : ResidualCache X) (q : SurfaceAncestorKey X)
    (hq : q ∈ cache.queries) : cache.lookup? q = some (residualTerms q) := by
  have hfind : cache.values.find? (fun t ↦ t.1 = q)
      (cache.matching_entries_subsingleton q) = some (q, residualTerms q) :=
    (Multiset.find?_eq_some_iff (cache.matching_entries_subsingleton q)).mpr
      ⟨(cache.mem_values_iff (q, residualTerms q)).mpr ⟨hq, rfl⟩, rfl⟩
  simp only [ResidualCache.lookup?, hfind, Option.map_some]

/-- A missing full key is distinguished from a cached scalar zero. -/
theorem ResidualCache.lookup?_of_not_mem (cache : ResidualCache X) (q : SurfaceAncestorKey X)
    (hq : q ∉ cache.queries) : cache.lookup? q = none := by
  have hfind : cache.values.find? (fun t ↦ t.1 = q)
      (cache.matching_entries_subsingleton q) = none := by
    apply (Multiset.find?_eq_none_iff (cache.matching_entries_subsingleton q)).mpr
    intro t ht he
    apply hq
    rw [← he]
    exact ((cache.mem_values_iff t).mp ht).1
  simp only [ResidualCache.lookup?, hfind, Option.map_none]

/-- The lookup has the same complete specification as the pre-existing cache. -/
theorem ResidualCache.lookup?_eq (cache : ResidualCache X) (q : SurfaceAncestorKey X) :
    cache.lookup? q = if q ∈ cache.queries then some (residualTerms q) else none := by
  by_cases hq : q ∈ cache.queries
  · rw [cache.lookup?_of_mem q hq, if_pos hq]
  · rw [cache.lookup?_of_not_mem q hq, if_neg hq]

/-- Only dimension-compatible lower-genus expressions are read as scalars.
The explicit option match avoids evaluating a fallback on cache hits. -/
def cachedLowerValueLookupWithPoints (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  if q.DimensionCompatible ∧ q.genus ≤ 1 then
    match cache.lookup? q with
    | some p => RationalTerms.eval (fun _ ↦ (0 : ℚ)) p
    | none => SurfaceLowGenusPointCache.componentValue X v₀ v₁ q
  else SurfaceLowGenusPointCache.componentValue X v₀ v₁ q

/-- Incomplete caches retain the original component at every supported or unsupported key. -/
theorem cachedLowerValueLookupWithPoints_eq (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (h₀ : v₀ = SurfaceGenusZero.pointValue X)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) (q : SurfaceAncestorKey X) :
    cachedLowerValueLookupWithPoints X cache v₀ v₁ q =
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q := by
  by_cases h : q.DimensionCompatible ∧ q.genus ≤ 1
  · rw [cachedLowerValueLookupWithPoints, if_pos h, cache.lookup?_eq q]
    by_cases hq : q ∈ cache.queries
    · simp only [if_pos hq, residualTerms, if_pos h.1, if_pos h.2,
        RationalTerms.eval_term, Multiset.map_zero, Multiset.prod_zero,
        Algebra.algebraMap_self_apply, mul_one]
    · rw [if_neg hq]
      exact congrFun (SurfaceLowGenusPointCache.componentValue_eq X v₀ v₁ h₀ h₁) q
  · rw [cachedLowerValueLookupWithPoints, if_neg h]
    exact congrFun (SurfaceLowGenusPointCache.componentValue_eq X v₀ v₁ h₀ h₁) q

/-- The new lookup is an implementation of the same existing certified scalar API. -/
theorem cachedLowerValueLookupWithPoints_eq_cached (X : SurfaceTarget)
    (cache : ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (q : SurfaceAncestorKey X) :
    cachedLowerValueLookupWithPoints X cache v₀ v₁ q = cachedLowerValue cache q :=
  (cachedLowerValueLookupWithPoints_eq X cache v₀ v₁ h₀ h₁ q).trans
    (cachedLowerValue_eq cache q).symm

/-- The original constant guards with first-match lookup into the unchanged cache. -/
def constantVertexWithPointLookup (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    if g ≤ 1 then
      let q := SurfaceAncestorKey.ofLabels g S h beta k a
      if q.DimensionCompatible then cachedLowerValueLookupWithPoints X cache v₀ v₁ q else 0
    else 0

theorem constantVertexWithPointLookup_eq (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (h₀ : v₀ = SurfaceGenusZero.pointValue X)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) :
    constantVertexWithPointLookup X cache v₀ v₁ = constantVertex X := by
  funext g S inst h beta k a
  simp only [constantVertexWithPointLookup, constantVertex,
    cachedLowerValueLookupWithPoints_eq X cache v₀ v₁ h₀ h₁]

/-- Every signed pullback, full class split, node state and coefficient is retained. -/
def guardedConstantPointContractionWithPointLookup (X : SurfaceTarget) (cache : ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) {g : ℕ} {S : Type} [Fintype S]
    (z : GluingExpression.CotangentTerm g S) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) : ℚ :=
  if 2 ≤ z.expression.maxComponentGenus then 0 else
    z.expression.scalarPointContraction X
      (SurfacePointPullback.vertex X (constantVertexWithPointLookup X cache v₀ v₁))
      z.decoration z.labels beta n a

theorem guardedConstantPointContractionWithPointLookup_eq (X : SurfaceTarget)
    (cache : ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    {g : ℕ} {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    guardedConstantPointContractionWithPointLookup X cache v₀ v₁ z beta n a =
      guardedConstantPointContraction X z beta n a := by
  rw [guardedConstantPointContractionWithPointLookup,
    constantVertexWithPointLookup_eq X cache v₀ v₁ h₀ h₁]
  rfl

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.L24Relation

def pointConstantWithPointLookup (X : SurfaceTarget) (cache : SurfaceGenusTwo.ResidualCache X)
    (v₀ v₁ : X.Curve → ℚ) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  (cotangentRelation.map fun t ↦ t.1 *
    SurfaceGenusTwo.guardedConstantPointContractionWithPointLookup X cache v₀ v₁
      t.2 beta n a).sum

theorem pointConstantWithPointLookup_eq (X : SurfaceTarget)
    (cache : SurfaceGenusTwo.ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPointLookup X cache v₀ v₁ n beta a = pointConstant X n beta a := by
  rw [← pointConstantGuarded_eq X n beta a]
  simp only [pointConstantWithPointLookup, pointConstantGuarded,
    SurfaceGenusTwo.guardedConstantPointContractionWithPointLookup_eq X cache v₀ v₁ h₀ h₁]

theorem pointConstantWithPointLookup_eq_normalized (X : SurfaceTarget)
    (cache : SurfaceGenusTwo.ResidualCache X) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPointLookup X cache v₀ v₁ n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) :=
  (pointConstantWithPointLookup_eq X cache v₀ v₁ h₀ h₁ n beta a).trans
    (pointConstant_eq_normalized X n beta a)

end AxiomaticGW.L24Relation
