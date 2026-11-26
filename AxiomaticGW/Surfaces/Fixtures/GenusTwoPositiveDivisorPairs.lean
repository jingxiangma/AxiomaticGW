/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoTwoMarkingProduct
public import AxiomaticGW.Surfaces.GenusTwoPrimitivePairTransfer
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1ExceptionalOneMarkingRequest
public import AxiomaticGW.Surfaces.PointBenchmarkCache
public import AxiomaticGW.Surfaces.LowGenusPointCache

/-! # Two first descendants of divisors in primitive blowup classes

The mixed transfer retains a rational calibration tail on either marking.
The positive-class ancestor is evaluated against the complete two-marked product relation.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoPositiveDivisorPairs
open SurfaceGenusTwo SurfacePointBenchmarkCache
variable {X : SurfaceTarget}

/-- Use certified primary caches on lower-genus vertices and the specified terminal
on a dimension-compatible genus-two component. -/
def vertex (base : SurfaceAncestorKey X → ℚ) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q.DimensionCompatible then
      if g ≤ 1 then SurfaceLowGenusPointCache.componentValue X (genusZero X) (genusOne X) q
      else base q
    else 0

theorem vertex_eq (base : SurfaceAncestorKey X → ℚ) : vertex base = productVertex base := by
  funext g S inst h beta k a
  by_cases hg : g ≤ 1 <;> simp only [vertex, productVertex, vertexTerms, residualTerms,
    SurfaceAncestorKey.ofLabels, hg, if_true, if_false,
    SurfaceLowGenusPointCache.componentValue_eq X _ _ (genusZero_eq X) (genusOne_eq X)]
  all_goals split_ifs <;> simp only [RationalTerms.eval_term,
    RationalTerms.eval_zero, Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, one_mul, mul_one]

namespace HirzebruchOne
open BlowupF1ExceptionalOneMarkingRequest SurfaceGenusTwoBlowupDescendants

private abbrev E : SurfaceBasisLabel .hirzebruchOne := .exceptional 0
private abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary
private abbrev highKey := pairKey exceptional ⟨E, 1⟩ ⟨E, 1⟩
private abbrev tailKey := pairKey (X := .hirzebruchOne) 0 ⟨E, 0⟩ ⟨E, 1⟩

/-- Both markings carry the first descendant of the exceptional curve divisor. -/
def exceptionalPair : SurfaceQuery .hirzebruchOne :=
  ⟨2, exceptional, [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩]⟩

set_option maxRecDepth 65536

private theorem mixed_terms :
    SurfaceDescendant.mixedAncestorTerms 2 (Fin 2) (by norm_num [StableArity]) (List.finRange 2)
      exceptional
      (fun _ ↦ 1) 0 (fun _ ↦ E) =
    RationalTerms.term 1 {highKey} + RationalTerms.term (-1) {tailKey} +
      RationalTerms.term (-1) {tailKey} := by
  rw [mixed_firstPair_primitive exceptional (by decide +kernel)]
  decide +kernel

private theorem product_eq : SurfaceGenusTwo.ancestorValue low highKey =
    ∑ i, productGraph (vertex low) exceptional (fun _ ↦ E) i := by
  rw [vertex_eq]
  exact ancestorValue_twoMarking_product low highKey rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (fun _ ↦ E) (by decide +kernel) (by decide +kernel)


private def weightedValues : Fin 25 → ℚ :=
  ![-1/960, -161/25920, -161/25920, 5/324, 0, 0, 0, 0, 0, 0, 0, 13/17280, 0,
    7/432, -67/8640, -67/8640, 0, 0, 0, 0, 0, 0, 0, 37/17280, 1/720]

set_option maxHeartbeats 1600000 in
-- Each kernel reduction contracts one of the 25 fully decorated graphs.
private theorem graph_value (i : Fin 25) :
    productGraph (vertex low) exceptional (fun _ ↦ E) i = weightedValues i := by
  fin_cases i <;> decide +kernel

private theorem tail_zero : low tailKey = 0 := by decide +kernel

/-- The two nonzero first calibration coefficients contribute the same class-zero
ancestor, whose normalization vanishes. The original descendant value is 1/144. -/
theorem exceptionalPair_value : queryValue? 0 exceptionalPair = some (1/144) := by
  rw [← queryValueWith?_eq_of_table 0 1 boundary boundary_eq_values exceptionalPair
    (by decide +kernel)]
  change some (RationalTerms.eval (ancestorValueWith boundary)
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin 2) _ (List.finRange 2) exceptional _ _ _)) = _
  have ht := mixed_terms
  convert_to some (RationalTerms.eval (ancestorValueWith boundary)
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin 2) (by norm_num [StableArity]) (List.finRange 2)
      exceptional (fun _ ↦ 1) 0 (fun _ ↦ E))) = _ using 1
  · congr 3 <;> funext j <;> fin_cases j <;> rfl
  rw [ht]
  simp only [RationalTerms.eval_add, RationalTerms.eval_term, Algebra.algebraMap_self_apply,
    Multiset.map_singleton, Multiset.prod_singleton, one_mul, neg_one_mul]
  change some (SurfaceGenusTwo.ancestorValue low highKey +
    -SurfaceGenusTwo.ancestorValue low tailKey + -SurfaceGenusTwo.ancestorValue low tailKey) = _
  rw [ancestorValue_low low tailKey rfl (by decide +kernel), tail_zero, product_eq]
  simp only [graph_value]
  decide +kernel

end HirzebruchOne
end AxiomaticGW.SurfaceGenusTwoPositiveDivisorPairs
