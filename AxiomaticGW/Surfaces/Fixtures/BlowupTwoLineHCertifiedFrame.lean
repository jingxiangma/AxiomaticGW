/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHComponents
public import AxiomaticGW.Surfaces.ZeroPointPrimaryGraph

/-! # Computing the original Bl₂ line terms with certified components

Undecorated graphs use the dimension-pruned primary evaluator. In a
decorated graph, the original full ancestor query determines the cached
component; undecorated vertices still use their primary scalar.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH
open SurfaceGenusTwo SurfacePointBenchmarkCache SurfaceLowGenusPointCache

private abbrev X := SurfaceTarget.blowupTwo

/-- Certified scalar input for the Bl₂ line contraction. -/
def componentVertex : SurfaceCotangentVertexValues .blowupTwo ℚ :=
  fun g S _ h d _ beta a ↦
    if g ≤ 1 then
      if d = 0 then SurfaceGenusOne.primaryScalar .blowupTwo
        (genusZero _) (genusOne _) g beta 0 a
      else let q := SurfaceAncestorKey.ofLabels g S h beta d a
           if q.DimensionCompatible then Components.cached q else 0
    else 0

private theorem lower_eq_original :
    lowerVertex = SurfacePointPullback.vertex X (constantVertex X) 0 := by
  funext g S inst h d l beta a
  simp only [lowerVertex, SurfacePointPullback.vertex, constantVertex,
    scalarComponentValue_eq, componentValue_eq X _ _ (genusZero_eq _) (genusOne_eq _)]

private theorem componentVertex_eq : componentVertex = lowerVertex := by
  funext g S inst h d l beta a
  by_cases hg : g ≤ 1
  · by_cases hd : d = 0
    · subst d
      rw [lower_eq_original, vertex_primary_constant_eq X g hg]
      simp only [componentVertex, if_pos hg, ite_true, genusZero_eq, genusOne_eq]
    · simp only [componentVertex, lowerVertex, if_pos hg, if_neg hd, Components.cached_eq]
  · simp only [componentVertex, lowerVertex, if_neg hg]

/-- Replay one complete original weighted position. -/
def cachedWeighted (j : Fin 815) : ℚ :=
  let z := L24Gluing.term j
  let w := L24CorrectionsReplay.fullClaim j
  if w = 0 ∨ 2 ≤ z.expression.maxComponentGenus then 0
  else if z.expression.noCotangent z.decoration then
    w * SurfaceGenusOne.primaryGraphDimensionEval .blowupTwo (genusZero _) (genusOne _)
      z.expression shifted 0 labels
  else w * z.expression.zeroPointContraction .blowupTwo componentVertex
      z.decoration z.labels shifted labels

/-- Cached values and dimension selection preserve the complete graph at the same index. -/
theorem cachedWeighted_eq (j : Fin 815) : cachedWeighted j = weighted j := by
  simp only [cachedWeighted, weighted, componentVertex_eq]
  split_ifs with hz hp
  · rfl
  · have hg : (L24Gluing.term j).expression.maxComponentGenus ≤ 1 := by omega
    rw [lower_eq_original, GluingExpression.primaryGraph_eq_zeroPoint X _ _ (genusZero_eq _)
      (genusOne_eq _) _ _ _ _ _ hg hp]
  · rfl

end AxiomaticGW.BlowupTwoLineH
