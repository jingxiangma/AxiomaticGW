/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.HReduction
public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Third
public import AxiomaticGW.Surfaces.ZeroPointPrimaryGraph

/-! # The original 815 shifted ruling graphs with one additional point

The complete L24 source is evaluated on its full effective class. Reducing a
primary graph to its primary scalar form preserves the labelled additional
point. Graphs with decorated vertices retain their signed point pullbacks.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.H
open SurfaceGenusTwo SurfacePointBenchmarkCache SurfaceGenusTwoPositiveSquare
open _root_.AxiomaticGW.BlowupTwoLineH (labels)

private theorem lower_root (c : CertifiedComponents X) :
    c.vertex (fun _ ↦ 0) = constantVertex X := by
  rw [← constantVertexWithPoints_eq X (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X),
    c.vertex_eq]
  funext g S inst h b k a
  by_cases hg : g ≤ 1
  · simp only [component, constantVertexWithPoints, if_pos hg,
      SurfaceLowGenusPointCache.scalarComponentValue_eq]
  · simp only [component, constantVertexWithPoints, if_neg hg, ite_self]

/-- The pullback of extra labelled points, with the original lower-genus numerics. -/
def lowerVertex (c : CertifiedComponents X) (n : ℕ) : SurfaceCotangentVertexValues X ℚ :=
  fun g S _ h d l b a ↦ if g ≤ 1 ∧ d = 0 then
    SurfaceGenusOne.primaryScalar X (genusZero X) (genusOne X) g b n a
  else SurfacePointPullback.vertex X (c.vertex (fun _ ↦ 0)) n g S h d l b a

/-- The optimized lower vertex is the original point pullback for every marked input. -/
theorem lowerVertex_eq (c : CertifiedComponents X) :
    lowerVertex c = SurfacePointPullback.vertex X (constantVertex X) := by
  rw [← primaryConstantPointVertex_eq X (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  funext n g S inst h d l b a
  simp only [lowerVertex, primaryConstantPointVertex, lower_root]

/-- The numerical lower vertex is the complete point pullback of the same certified backend. -/
theorem lowerVertex_eq_pullback (c : CertifiedComponents X) :
    lowerVertex c = SurfacePointPullback.vertex X (c.vertex (fun _ ↦ 0)) := by
  rw [lowerVertex_eq, lower_root]

/-- Weighted lower-genus contraction before summing over all 815 source positions. -/
def weighted (c : CertifiedComponents X) (i : Fin 2) (j : Fin 815) : ℚ :=
  let z := L24Gluing.term j
  let w := L24CorrectionsReplay.fullClaim j
  if w = 0 ∨ 2 ≤ z.expression.maxComponentGenus then 0 else
  if z.expression.noCotangent z.decoration then
    w * SurfaceGenusOne.primaryGraphDimensionEval X (genusZero X) (genusOne X)
      z.expression (shifted i) 1 labels
  else w * z.expression.scalarPointContraction X (lowerVertex c)
    z.decoration z.labels (shifted i) 1 labels

/-- The original pivot constant is the complete weighted shifted graph sum. -/
theorem constant_eq_sum (c : CertifiedComponents X) (i : Fin 2) :
    SurfaceGenusTwoBlowupScalar.constant 0 (state i) = ∑ j, weighted c i j := by
  have he : X.effective.energy (curve i) = 2 := by fin_cases i <;> decide +kernel
  rw [state, SurfaceGenusTwoBlowupScalar.constant, he, show (2 : ℕ) - 1 = 1 from rfl,
    L24Relation.pointConstantGuarded_eq_fullFrame]
  apply Finset.sum_congr rfl
  intro j _
  let z := L24Gluing.term j
  change L24CorrectionsReplay.fullClaim j *
    guardedConstantPointContraction X z (shifted i) 1 labels = _
  rcases eq_or_ne (L24CorrectionsReplay.fullClaim j) 0 with hw | hw
  · simp only [weighted, hw, true_or, if_true, zero_mul]
  by_cases hg : 2 ≤ z.expression.maxComponentGenus
  · simp only [weighted, guardedConstantPointContraction, z, hg, or_true, if_true, mul_zero]
  have hl : z.expression.maxComponentGenus ≤ 1 := by omega
  have primary := primaryConstantPointVertex_eq X (genusZero X) (genusOne X)
    (genusZero_eq X) (genusOne_eq X)
  unfold weighted
  change _ = (if _ ∨ 2 ≤ z.expression.maxComponentGenus then _ else _)
  rw [if_neg (not_or_intro hw hg)]
  unfold guardedConstantPointContraction
  rw [if_neg hg]
  by_cases hd : z.expression.noCotangent z.decoration = true
  · rw [if_pos hd, (GluingExpression.noCotangent_eq_true _ _).mp hd,
      SurfaceGenusOne.primaryGraphDimensionEval_eq,
      primaryGraphEval_pointContraction_eq X _ _ _ hl z.labels, primary,
      GluingExpression.scalarPointContraction_eq]
  · rw [if_neg hd]
    simp only [lowerVertex_eq, z]

end AxiomaticGW.BlowupTwoRuling.H
