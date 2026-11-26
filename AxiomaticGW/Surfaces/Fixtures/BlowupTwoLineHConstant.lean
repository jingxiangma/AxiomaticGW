/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHDivisors
public import AxiomaticGW.Surfaces.GenusTwoL24FullFrame
public import AxiomaticGW.Surfaces.ScalarAncestorStep

/-!
# Lower-genus terms in the Bl₂ strict-transform line equation

Each entry retains its original corrected L24 coefficient and decorated
expression. The genus-two guard and the exact zero-point contraction leave
only lower-genus terminal values, computed with the certified point backends.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH
open BlowupTwoLineBP SurfaceGenusTwo SurfacePointBenchmarkCache

/-- The guarded low-genus terminal using effective-coordinate sums inside ancestor steps. -/
def lowerVertex : SurfaceCotangentVertexValues .blowupTwo ℚ := fun g S _ h d _ beta a ↦
  if g ≤ 1 then
    let q := SurfaceAncestorKey.ofLabels g S h beta d a
    if q.DimensionCompatible then
      SurfaceLowGenusPointCache.scalarComponentValue .blowupTwo (genusZero _) (genusOne _) q
    else 0
  else 0

private theorem lowerVertex_eq : lowerVertex = SurfacePointPullback.vertex .blowupTwo
    (constantVertexWithPoints .blowupTwo (genusZero _) (genusOne _)) 0 := by
  funext g S inst h d l beta a
  simp only [lowerVertex, SurfacePointPullback.vertex, constantVertexWithPoints,
    SurfaceLowGenusPointCache.scalarComponentValue_eq]

/-- One of the 815 original positions in the lower-genus constant. -/
def weighted (j : Fin 815) : ℚ :=
  let z := L24Gluing.term j
  let w := L24CorrectionsReplay.fullClaim j
  if w = 0 ∨ 2 ≤ z.expression.maxComponentGenus then 0 else
    w * z.expression.zeroPointContraction .blowupTwo lowerVertex
      z.decoration z.labels shifted labels

/-- The original constant is the sum of all retained weighted contractions. -/
theorem constant_eq_sum :
    SurfaceGenusTwoBlowupScalar.constant 0 (line, .hyperplane) = ∑ j, weighted j := by
  have he : SurfaceTarget.blowupTwo.effective.energy line = 1 := by decide +kernel
  have hs : line + SurfaceTarget.blowupTwo.exceptionalCurve 0 = shifted := by decide +kernel
  rw [SurfaceGenusTwoBlowupScalar.constant, he, Nat.sub_self, hs,
    L24Relation.pointConstantGuarded_eq_fullFrame]
  apply Finset.sum_congr rfl
  intro j _
  let z := L24Gluing.term j
  change L24CorrectionsReplay.fullClaim j *
    guardedConstantPointContraction .blowupTwo z shifted 0 labels = _
  rcases eq_or_ne (L24CorrectionsReplay.fullClaim j) 0 with h | h
  · simp only [weighted, h, true_or, if_true, zero_mul]
  · rw [← guardedConstantPointContractionWithPoints_eq .blowupTwo
      (genusZero .blowupTwo) (genusOne .blowupTwo) (genusZero_eq _) (genusOne_eq _)]
    by_cases hz : 2 ≤ z.expression.maxComponentGenus
    · simp only [weighted, guardedConstantPointContractionWithPoints, z, hz, or_true, if_true,
        mul_zero] at *
    · simp only [weighted, guardedConstantPointContractionWithPoints, h, false_or,
        lowerVertex_eq, GluingExpression.scalarPointContraction_eq,
        GluingExpression.zeroPointContraction_eq, z]
      rw [if_neg hz, if_neg hz]

end AxiomaticGW.BlowupTwoLineH
