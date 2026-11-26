/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCachedAncestors

/-!
# Reusing certified components inside elliptic ancestor steps

The genus-two replay also repeats rational and elliptic dependencies inside
its elliptic components. The same certified residual cache can supply these
values. A missing key retains the original algorithm, including outside the
dimension-compatible lower-genus sector; no cache-completeness assumption is
needed. Each final elliptic step still checks the original full contraction.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne
variable {X : SurfaceTarget}

/-- The sufficient-fuel evaluator satisfies its original elliptic equation. -/
theorem ancestorValue_eq_step (q : SurfaceAncestorKey X) (hg : q.genus = 1)
    (hp : ¬q.IsPrimary) :
    ancestorValue X q = ancestorStep (ancestorValue X) q hg hp := by
  rw [ancestorValue, ancestorValueFuel_stable q.totalPsi (q.totalPsi + 1) q hg le_rfl
    (Nat.le_succ _), ancestorValueFuel, dif_pos hg, dif_neg hp]
  apply ancestorStep_congr
  intro q' hg' hdegree
  exact ancestorValueFuel_stable q.totalPsi q'.totalPsi q' hg' (by omega) le_rfl

end AxiomaticGW.SurfaceGenusOne

namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- Interpret a stored scalar component only in the sector where residual
expressions are scalar; every other key uses the original algorithm. -/
def cachedLowerValue (cache : ResidualCache X) (q : SurfaceAncestorKey X) : ℚ :=
  if q.DimensionCompatible ∧ q.genus ≤ 1 ∧ q ∈ cache.queries then
    RationalTerms.eval (fun _ ↦ (0 : ℚ))
      ((cache.values.map fun t ↦ if t.1 = q then t.2 else 0).sum)
  else SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q

/-- No value is inferred from a missing key or a dimension-incompatible residual. -/
theorem cachedLowerValue_eq (cache : ResidualCache X) (q : SurfaceAncestorKey X) :
    cachedLowerValue cache q =
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q := by
  unfold cachedLowerValue
  split_ifs with h
  · rw [cache.values_eq]
    simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum,
      Finset.sum_ite_eq', if_pos h.2.2, residualTerms, if_pos h.1, if_pos h.2.1,
      RationalTerms.eval_term, Multiset.map_zero, Multiset.prod_zero,
      Algebra.algebraMap_self_apply, mul_one]
  · rfl

/-- The unchanged loop and separating-tail sum with certified component values. -/
def ellipticStepCached (cache : ResidualCache X) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map fun t ↦
    t.1 * t.2.surfaceEval X
      (fun g S _ h beta k a ↦ cachedLowerValue cache
        (SurfaceAncestorKey.ofLabels g S h beta k a))
      q.beta (SurfaceGenusOne.lowerAncestorPowers q hg hp)
        (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp)).sum

/-- A partial component cache computes the original elliptic ancestor. -/
theorem ellipticStepCached_eq (cache : ResidualCache X) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    ellipticStepCached cache q hg hp = SurfaceGenusOne.ancestorValue X q := by
  rw [SurfaceGenusOne.ancestorValue_eq_step q hg hp]
  simp only [ellipticStepCached, SurfaceGenusOne.ancestorStep, cachedLowerValue_eq]

end AxiomaticGW.SurfaceGenusTwo
