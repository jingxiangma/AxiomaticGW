/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineBPEquation
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHReduction

/-! # The eight lower canonical columns in the shifted hyperplane equation for 2L

The three nonzero class-zero seeds and the five families on E₁+L use the same 27 original
genus-two graphs. Each column has its own normalized insertion and effective remainder.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineBP.Shifted
open SurfaceGenusTwo SurfaceGenusTwoBlowupHUniform SurfacePolynomialReduction
open SurfaceGenusTwoBlowupScalar

abbrev X := SurfaceTarget.blowupTwo
abbrev ruling : X.Curve := ![1, 0, 1]
abbrev line : X.Curve := ![0, 0, 1]

/-- The strict-line hyperplane row is evaluated at E₁ + 2L. -/
abbrev shifted : X.Curve := ![1, 0, 2]
abbrev labels : Fin 4 → SurfaceBasisLabel X := BlowupTwoLineH.labels
def descendantLabel : Fin 8 → SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional 0, .exceptional 1, .hyperplane, .point, .unit,
    .exceptional 0, .exceptional 1]
def pointCount (j : Fin 8) := if j.val < 3 then 0 else if j.val = 4 then 1 else 2
def columnClass (j : Fin 8) : X.Curve := if j.val < 3 then 0 else ruling
def remainderClass (j : Fin 8) : X.Curve := if j.val < 3 then shifted else line

/-- Three constant-curve divisor seeds, followed by H, P, N, K₁, K₂ on E₁+L. -/
def column (j : Fin 8) : Variable X :=
  if j.val = 5 then .inr (SurfaceQuery.points X 2 ruling 3)
  else .inr (SurfaceFirstDescendant.query 2 (columnClass j) (descendantLabel j) (pointCount j))
def terminal (j : Fin 8) : SurfaceVertexValues X ℚ :=
  if j.val = 5 then coefficientVertex X (column j)
  else firstCoefficientVertex X (columnClass j) (descendantLabel j) (pointCount j)

/-- An individual signed original diagram at the effective remainder of its column. -/
def weighted (j : Fin 8) (k : Fin 815) :=
  L24CorrectionsReplay.fullClaim k *
    remainderPointCoefficient X (column j) (terminal j) (L24Gluing.term k)
      (remainderClass j) 1 labels

private theorem terminal_eq (j : Fin 8) : terminal j = coefficientVertex X (column j) := by
  by_cases h : j.val = 5
  · simp only [terminal, h, if_true]
  · simp only [terminal, column, h, if_false, firstCoefficientVertex_eq]

/-- Original positions of the nonzero L24 terms carrying a genus-two component. -/
def sourceIndex : Fin 27 → Fin 815 :=
  ![51, 52, 56, 57, 59, 62, 63, 64, 66, 69, 70, 74, 76, 81, 83, 88, 93, 95, 97,
    101, 105, 109, 110, 112, 113, 119, 120]

set_option maxRecDepth 32768 in
/-- The complete original column is the sum of the 27 signed genus-two contractions. -/
theorem exact_frame (j : Fin 8) :
    singletonCoefficient 0 (BlowupTwoDoubleLine.curve, .hyperplane) (column j) =
      ∑ k : Fin 27, weighted j (sourceIndex k) := by
  change L24Relation.pointCoefficient X (X.effective.energy BlowupTwoDoubleLine.curve - 1)
    (BlowupTwoDoubleLine.curve + X.exceptionalCurve 0) labels (column j) = _
  rw [show X.effective.energy BlowupTwoDoubleLine.curve - 1 = 1 by decide +kernel,
    show BlowupTwoDoubleLine.curve + X.exceptionalCurve 0 = shifted by decide +kernel]
  simp only [L24Relation.pointCoefficient, L24Relation.cotangentRelation,
    Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  have frame : genusTwoFrame = Finset.univ.image sourceIndex := by decide +kernel
  have inj : Function.Injective sourceIndex := by
    change ∀ a b, sourceIndex a = sourceIndex b → a = b
    decide +kernel
  trans ∑ k ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim k *
      SurfaceGenusTwo.pointCoefficient X (column j) (L24Gluing.term k) shifted 1 labels
  · symm
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((genusTwoFrame_checked k).mp hk).1⟩
    · intro k hk hnot
      have hn : (L24Gluing.term k).expression.maxComponentGenus ≠ 2 := fun h ↦
        hnot ((genusTwoFrame_checked k).mpr ⟨(Finset.mem_filter.mp hk).2, h⟩)
      rw [SurfaceGenusTwo.pointCoefficient, if_neg hn, mul_zero]
  · rw [frame, Finset.sum_image (fun _ _ _ _ e ↦ inj e)]
    apply Finset.sum_congr rfl
    intro k _
    have eqc : SurfaceGenusZero.variableCurve (column j) + remainderClass j = shifted := by
      fin_cases j <;> decide +kernel
    rw [weighted, remainderPointCoefficient_eq X (column j) (terminal j)
      (terminal_eq j), eqc]

/-- Complete weighted sum of the original genus-two source positions in the selected column. -/
def coefficient (j : Fin 8) : ℚ := ∑ k : Fin 27, weighted j (sourceIndex k)

/-- The original shifted hyperplane value expressed only in its lower constant, the three
nonzero class-zero seeds, and the five earlier states on the ruling. -/
theorem value_eq :
    actual (BlowupTwoDoubleLine.curve, .hyperplane) =
      constant 0 (BlowupTwoDoubleLine.curve, .hyperplane) -
        coefficient 0 / 960 - (coefficient 1 + coefficient 2) / 2880 +
        coefficient 3 * actual (ruling, .hyperplane) +
        coefficient 4 * actual (ruling, .point) +
        coefficient 5 * actual (ruling, .primary) +
        coefficient 6 * actual (ruling, .exceptional 0) +
        coefficient 7 * actual (ruling, .exceptional 1) := by
  let s : SurfaceGenusTwoBlowupOrder.State X := (BlowupTwoDoubleLine.curve, .hyperplane)
  let atClass (d : X.Curve) (j : Fin 5) :=
    singletonCoefficient 0 s (.inr ((BlowupTwoLineBP.canonicalFamily j).query d))
  have rulingCol (j : Fin 5) : atClass ruling j = coefficient (Fin.natAdd 3 j) := by
    have h : Sum.inr ((BlowupTwoLineBP.canonicalFamily j).query ruling) =
        column (Fin.natAdd 3 j) := by fin_cases j <;> decide +kernel
    exact (congrArg (singletonCoefficient 0 s) h).trans (exact_frame _)
  let source : Fin 3 → Fin 5 := ![0, 3, 4]
  have zeroCol (j : Fin 3) : atClass 0 (source j) = coefficient (j.castAdd 5) := by
    have h : Sum.inr ((BlowupTwoLineBP.canonicalFamily (source j)).query 0) =
        column (j.castAdd 5) := by fin_cases j <;> decide +kernel
    exact (congrArg (singletonCoefficient 0 s) h).trans (exact_frame _)
  have h := shifted_hyperplane_equation
  rw [Fin.sum_univ_five, Fin.sum_univ_five] at h
  change actual _ = constant 0 s + (atClass 0 (source 0) * (-1 / 960) +
    atClass 0 1 * 0 + atClass 0 2 * 0 + atClass 0 (source 1) * (-1 / 2880) +
    atClass 0 (source 2) * (-1 / 2880)) +
    (atClass ruling 0 * actual (ruling, .hyperplane) + atClass ruling 1 * actual (ruling, .point) +
    atClass ruling 2 * actual (ruling, .primary) +
    atClass ruling 3 * actual (ruling, .exceptional 0) +
    atClass ruling 4 * actual (ruling, .exceptional 1)) at h
  simp only [zeroCol, rulingCol, mul_zero, add_zero] at h
  change actual _ = constant 0 s + (coefficient 0 * (-1 / 960) +
    coefficient 1 * (-1 / 2880) + coefficient 2 * (-1 / 2880)) +
    (coefficient 3 * actual (ruling, .hyperplane) + coefficient 4 * actual (ruling, .point) +
    coefficient 5 * actual (ruling, .primary) + coefficient 6 * actual (ruling, .exceptional 0) +
    coefficient 7 * actual (ruling, .exceptional 1)) at h
  rw [h]
  change constant 0 s + _ + _ = constant 0 s - _ - _ + _ + _ + _ + _ + _
  ring

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
-- Both full-curve remainders distribute the extra point over every node and cotangent tail.
/-- The node pairing and the original relation give opposite signs on these two nonzero
ruling contributions. Both are recomputed with the additional primary point. -/
theorem signed_ruling_terms : weighted 7 62 = -1 ∧ weighted 3 57 = 1 / 2 := by
  constructor <;> decide +kernel

end AxiomaticGW.BlowupTwoDoubleLineBP.Shifted
