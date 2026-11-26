/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineReduction
public import AxiomaticGW.Surfaces.GenusTwoL24FullFrame
public import AxiomaticGW.Surfaces.GenusTwoBlowupHUniform
public import AxiomaticGW.Surfaces.GenusTwoL24PointCache
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-! # Original shifted L24 reduction for the pullback line on the one-point blowup

Its source has full effective class 2E+F and two extra point markings. Only
the two class-zero divisor coefficients contribute below the hyperplane pivot.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLine
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar SurfacePolynomialReduction
open SurfaceGenusTwo SurfacePointBenchmarkCache

def shifted : X.Curve := ![2,1]
def labels : Fin 4 → SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]

set_option maxRecDepth 20000

private theorem hyperplane_pivot :
    singletonCoefficient 0 (line, .hyperplane) (.inr ((Family.hyperplane : Family X).query line)) =
      -1 := by
  rw [singletonCoefficient_eq, ← SurfaceGenusTwoBlowupOrderedCertificate.pivot_eq 0
    (line, .hyperplane) (by change 0 < X.planeDegree line; decide +kernel)]
  rfl

private theorem hyperplane_other (f : Family X) (hf : f ≠ .hyperplane) :
    singletonCoefficient 0 (line, .hyperplane) (.inr (f.query line)) = 0 := by
  rw [singletonCoefficient_eq]
  by_contra h
  have hs := SurfaceGenusTwoBlowupHOtherFamilies.canonical_coefficient_support X 0
    line line f (by decide +kernel) h
  rcases hs with h | h
  · exact hf h.1
  · rw [earlier_iff] at h
    cases f <;> simp only [SurfaceGenusTwoBlowupOrder.Family.rank] at h <;> omega

/-- All 815 original positions, including the signed correction weights and all point placements. -/
def weighted (j : Fin 815) : ℚ :=
  let z := L24Gluing.term j
  let w := L24CorrectionsReplay.fullClaim j
  if w = 0 then 0 else w *
    guardedConstantPointContractionWithPoints X (genusZero X) (genusOne X) z shifted 2 labels

theorem constant_eq_sum : constant 0 (line, .hyperplane) = ∑ j, weighted j := by
  have he : X.effective.energy line = 3 := by decide +kernel
  have hs : line + X.exceptionalCurve 0 = shifted := by decide +kernel
  unfold constant
  rw [he, hs, L24Relation.pointConstantGuarded_eq_fullFrame]
  apply Finset.sum_congr rfl
  intro j _
  unfold weighted
  by_cases h : L24CorrectionsReplay.fullClaim j = 0
  · simp only [h, if_true, zero_mul]
  · simp only [if_neg h, guardedConstantPointContractionWithPoints_eq X _ _ (genusZero_eq X)
      (genusOne_eq X), labels, Nat.reduceSub]


/-- Positions surviving the nonzero-weight and lower-genus tests. -/
def activeFrame : Finset (Fin 815) :=
  (Finset.univ.filter fun j ↦ L24CorrectionsReplay.fullClaim j ≠ 0) \
    SurfaceGenusTwoBlowupHUniform.genusTwoFrame

theorem activeFrame_card : activeFrame.card = 694 := by decide +kernel

/-- Exactly 121 positions can be discarded before numerical evaluation. -/
theorem constant_eq_active : constant 0 (line, .hyperplane) = ∑ j ∈ activeFrame, weighted j := by
  rw [constant_eq_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  by_cases hz : L24CorrectionsReplay.fullClaim j = 0
  · simp only [weighted, hz, ite_true]
  · have hg : j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame := by
      by_contra h
      exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hz⟩, h⟩)
    have hu := ((SurfaceGenusTwoBlowupHUniform.genusTwoFrame_checked j).mp hg).2
    simp only [weighted, if_neg hz, guardedConstantPointContractionWithPoints, hu, le_refl,
      ite_true, mul_zero]

/-- The two class-zero divisor coefficients use the twenty-seven original genus-two positions. -/
def divisorCoefficient (b : SurfaceBasisLabel X) : ℚ :=
  ∑ j ∈ SurfaceGenusTwoBlowupHUniform.genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    remainderPointCoefficient X (.inr (SurfaceFirstDescendant.query 2 0 b 0))
      (firstCoefficientVertex X 0 b 0) (L24Gluing.term j) shifted 2 labels

open SurfaceGenusTwoBlowupHUniform in
theorem divisorCoefficient_eq (b : SurfaceBasisLabel X) :
    divisorCoefficient b =
      singletonCoefficient 0 (line, .hyperplane) (.inr (SurfaceFirstDescendant.query 2 0 b 0)) := by
  let col : Variable X := .inr (SurfaceFirstDescendant.query 2 0 b 0)
  have he : X.effective.energy line = 3 := by decide +kernel
  have hs : line + X.exceptionalCurve 0 = shifted := by decide +kernel
  simp only [singletonCoefficient, he, Nat.reduceSub, hs, L24Relation.pointCoefficient,
    L24Relation.cotangentRelation, Multiset.map_map, Function.comp_def,
    ← Finset.sum_eq_multiset_sum]
  trans ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.pointCoefficient X col (L24Gluing.term j) shifted 2 labels
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [remainderPointCoefficient_eq X col (firstCoefficientVertex X 0 b 0)
      (firstCoefficientVertex_eq (X := X) 0 b 0) (L24Gluing.term j) shifted 2 labels]
    change SurfaceGenusTwo.pointCoefficient X col _ (0 + shifted) 2 _ = _
    rw [zero_add]
  · apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ((genusTwoFrame_checked j).mp hj).1⟩
    · intro j hj hnot
      have hne : (L24Gluing.term j).expression.maxComponentGenus ≠ 2 := fun h ↦
        hnot ((genusTwoFrame_checked j).mpr ⟨(Finset.mem_filter.mp hj).2, h⟩)
      rw [SurfaceGenusTwo.pointCoefficient, if_neg hne, mul_zero]

/-- The exact absolute H value is the shifted L24 constant minus its two original class-zero
coefficients times the known boundary magnitudes. -/
theorem hyperplane_residual : value (line, .hyperplane) =
    (∑ j, weighted j) -
      singletonCoefficient 0 (line, .hyperplane)
        (.inr ((Family.hyperplane : Family X).query 0)) / 960 -
      singletonCoefficient 0 (line, .hyperplane)
        (.inr ((Family.exceptional (X := X) 0).query 0)) / 2880 := by
  have h := reduced_row (.hyperplane : Family X)
  rw [Fin.sum_univ_four] at h
  change _ - _ / 960 - _ / 2880 +
    (singletonCoefficient 0 (line, .hyperplane)
        (.inr ((Family.hyperplane : Family X).query line)) * _ +
      singletonCoefficient 0 (line, .hyperplane) (.inr ((Family.point : Family X).query line)) * _ +
      singletonCoefficient 0 (line, .hyperplane)
        (.inr ((Family.primary : Family X).query line)) * _ +
      singletonCoefficient 0 (line, .hyperplane)
        (.inr ((Family.exceptional (X := X) 0).query line)) * _) = 0 at h
  rw [hyperplane_pivot, hyperplane_other .point (by intro h; cases h),
    hyperplane_other .primary (by intro h; cases h),
    hyperplane_other (.exceptional 0) (by intro h; cases h), constant_eq_sum] at h
  change _ - _ / 960 - _ / 2880 + (-1 * value (line,.hyperplane) + 0 * _ + 0 * _ + 0 * _) = 0 at h
  linarith only [h]

/-- A numeric proof needs only the signed sum of the original lower-genus graph contractions
and the two explicitly reduced divisor columns. -/
theorem hyperplane_eq_frame : value (line, .hyperplane) =
    (∑ j, weighted j) - divisorCoefficient .hyperplane / 960 -
      divisorCoefficient (.exceptional 0) / 2880 := by
  rw [hyperplane_residual, divisorCoefficient_eq, divisorCoefficient_eq]
  congr 2

end AxiomaticGW.F1PlaneLine
