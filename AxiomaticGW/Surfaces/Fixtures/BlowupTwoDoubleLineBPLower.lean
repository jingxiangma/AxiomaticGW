/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineBPShifted
public import AxiomaticGW.Surfaces.GenusTwoL24FullFrame
public import AxiomaticGW.Surfaces.ZeroPointPrimaryGraph

/-! # The full lower-genus constant in the shifted equation for twice the strict line

On an undecorated graph the required virtual dimensions determine the distribution of
the extra point. Decorated graphs retain the original signed cotangent pullback.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineBP.ShiftedLower
open SurfaceGenusTwo SurfacePointBenchmarkCache SurfaceGenusTwoBlowupScalar
open BlowupTwoDoubleLineBP.Shifted (X shifted labels)

/-- The guarded original weighted constant term, with primary dimension pruning whenever
all flags are undecorated. -/
def weighted (k : Fin 815) :=
  let z := L24Gluing.term k
  let w := L24CorrectionsReplay.fullClaim k
  if w = 0 ∨ 2 ≤ z.expression.maxComponentGenus then 0 else
    if z.expression.noCotangent z.decoration then
      w * SurfaceGenusOne.primaryGraphDimensionEval X (genusZero X) (genusOne X)
        z.expression shifted 1 labels
    else w * guardedConstantPointContractionWithPoints X (genusZero X) (genusOne X)
      z shifted 1 labels

set_option maxRecDepth 32768 in
/-- Both branches retain the signed marked contraction at this original graph position. -/
theorem weighted_eq (k : Fin 815) : weighted k = L24CorrectionsReplay.fullClaim k *
    guardedConstantPointContraction X (L24Gluing.term k) shifted 1 labels := by
  let z := L24Gluing.term k
  unfold weighted
  by_cases hw : L24CorrectionsReplay.fullClaim k = 0
  · simp only [hw, true_or, if_true, zero_mul]
  by_cases hg : 2 ≤ z.expression.maxComponentGenus
  · simp only [z] at hg
    simp only [hg, or_true, if_true, guardedConstantPointContraction, mul_zero]
  simp only [show ¬2 ≤ (L24Gluing.term k).expression.maxComponentGenus from hg,
    hw, or_self, if_false]
  by_cases hp : z.expression.noCotangent z.decoration = true
  · rw [if_pos hp, guardedConstantPointContraction, if_neg hg]
    congr 1
    rw [(GluingExpression.noCotangent_eq_true z.expression z.decoration).mp hp,
      GluingExpression.scalarPointContraction_eq, SurfaceGenusOne.primaryGraphDimensionEval_eq,
      primaryGraphEval_pointContraction_eq X (genusZero X) (genusOne X) z.expression (by omega),
      primaryConstantPointVertex_eq X (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  · rw [if_neg hp, guardedConstantPointContractionWithPoints_eq X (genusZero X) (genusOne X)
      (genusZero_eq X) (genusOne_eq X)]

/-- All 815 original terms in the lower constant of the shifted hyperplane equation. -/
theorem constant_eq : constant 0 (BlowupTwoDoubleLine.curve, .hyperplane) = ∑ k, weighted k := by
  change L24Relation.pointConstantGuarded X (X.effective.energy BlowupTwoDoubleLine.curve - 1)
    (BlowupTwoDoubleLine.curve + X.exceptionalCurve 0) labels = _
  rw [show X.effective.energy BlowupTwoDoubleLine.curve - 1 = 1 by decide +kernel,
    show BlowupTwoDoubleLine.curve + X.exceptionalCurve 0 = shifted by decide +kernel,
    L24Relation.pointConstantGuarded_eq_fullFrame]
  simp only [weighted_eq]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
-- Each graph verifies the sum over its full effective splittings and both branches of every node.
/-- Vanishing of three complete undecorated terms, including their inverse-metric sums. -/
theorem primary_cancellations : weighted 449 = 0 ∧ weighted 726 = 0 ∧ weighted 808 = 0 := by
  constructor
  · decide +kernel
  constructor <;> decide +kernel

/-- The weighted lower-genus positions still needed after the three primary cancellations. -/
def remaining : Finset (Fin 815) :=
  (Finset.univ.filter fun k ↦ L24CorrectionsReplay.fullClaim k ≠ 0 ∧
    (L24Gluing.term k).expression.maxComponentGenus ≤ 1) \ {449, 726, 808}

set_option maxRecDepth 32768 in
theorem remaining_card : remaining.card = 691 := by decide +kernel

/-- The other original positions have zero weight, carry a genus-two component, or are
one of the three explicitly verified complete primary contractions. -/
theorem constant_eq_remaining :
    constant 0 (BlowupTwoDoubleLine.curve, .hyperplane) = ∑ k ∈ remaining, weighted k := by
  rw [constant_eq]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hnot
  by_cases hw : L24CorrectionsReplay.fullClaim k = 0
  · simp only [weighted, hw, true_or, if_true]
  by_cases hg : 2 ≤ (L24Gluing.term k).expression.maxComponentGenus
  · simp only [weighted, hg, or_true, if_true]
  have hits : k ∈ ({449, 726, 808} : Finset (Fin 815)) := by
    by_contra hm
    exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hw, by omega⟩, hm⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hits
  rcases hits with rfl | rfl | rfl
  · exact primary_cancellations.1
  · exact primary_cancellations.2.1
  · exact primary_cancellations.2.2

end AxiomaticGW.BlowupTwoDoubleLineBP.ShiftedLower
