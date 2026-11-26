/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.DimensionSources
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ShiftedSources

/-! # Dimension-pruned original L24 sources of the shifted ruling H equations -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.H
open SurfaceGenusTwo SurfacePointBenchmarkCache SurfaceGenusTwoPositiveSquare GluingExpression
open _root_.AxiomaticGW.BlowupTwoLineH (labels)

/-- The graded scalar evaluator of a shifted graph, retaining the original primary shortcut. -/
def dimensionWeighted (c : CertifiedComponents X) (i : Fin 2) (j : Fin 815) : ℚ :=
  let z := L24Gluing.term j
  let w := L24CorrectionsReplay.fullClaim j
  if w = 0 ∨ 2 ≤ z.expression.maxComponentGenus then 0 else
  if z.expression.noCotangent z.decoration then
    w * SurfaceGenusOne.primaryGraphDimensionEval X (genusZero X) (genusOne X)
      z.expression (shifted i) 1 labels
  else w * z.expression.dimensionPointContraction X (lowerVertex c)
    z.decoration z.labels (shifted i) 1 labels

/-- Every pruned shifted source agrees with the original weighted L24 graph. -/
theorem dimensionWeighted_eq (c : CertifiedComponents X) (i : Fin 2) (j : Fin 815) :
    dimensionWeighted c i j = weighted c i j := by
  have hg : VertexPointDimension (lowerVertex c) := by
    rw [lowerVertex_eq_pullback]
    exact pointPullback_dimension (BlowupTwoRulingInterior.FullSquares.component_graded c _)
  simp only [dimensionWeighted, weighted, dimensionPointContraction_eq hg]

end AxiomaticGW.BlowupTwoRuling.H
