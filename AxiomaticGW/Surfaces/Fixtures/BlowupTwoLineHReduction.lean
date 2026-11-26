/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPConstants
public import AxiomaticGW.Surfaces.GenusTwoBlowupHUniform
public import AxiomaticGW.Surfaces.GenusTwoBlowupOrderedCertificate

/-!
# The shifted L24 hyperplane equation at the strict transform of the two-point line

For L = H − E₁ − E₂ the source is L + E₁ = H − E₂, with no extra points.
The order places only plane-degree-zero states before its H row. Exactly
three earlier canonical values are nonzero. Their divisor labels and the
chosen shift are retained by the twenty-seven genus-two graphs.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction SurfaceGenusTwoBlowupScalar
open SurfaceGenusTwoBlowupOrderedCertificate SurfaceGenusTwoBlowupHUniform SurfaceGenusTwo
open BlowupTwoLineBP

private abbrev X := SurfaceTarget.blowupTwo
private abbrev state : State X := (line, .hyperplane)

/-- The source after adding the first exceptional generator in effective coordinates. -/
abbrev shifted : SurfaceTarget.blowupTwo.Curve := ![1, 0, 1]

/-- Divisor insertions in the selected original shifted relation. -/
abbrev labels : Fin 4 → SurfaceBasisLabel .blowupTwo :=
  ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0]

/-- The class-zero first-descendant column at the specified basis label. -/
def zeroColumn (b : SurfaceBasisLabel .blowupTwo) : Variable .blowupTwo :=
  .inr (SurfaceFirstDescendant.query 2 0 b 0)

/-- Exact class-zero divisor coefficient with only the twenty-seven genus-two diagrams. -/
def divisorCoefficient (b : SurfaceBasisLabel .blowupTwo) : ℚ :=
  ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    remainderPointCoefficient .blowupTwo (zeroColumn b) (firstCoefficientVertex .blowupTwo 0 b 0)
      (L24Gluing.term j) shifted 0 labels

private theorem energy_line : X.effective.energy line = 1 := by decide +kernel
private theorem degree_line : X.planeDegree line = 1 := by decide +kernel
private theorem shift_line : line + X.exceptionalCurve 0 = shifted := by decide +kernel

/-- Each divisor coefficient belongs to the complete canonical H row. -/
theorem divisorCoefficient_eq (b : SurfaceBasisLabel .blowupTwo) :
    divisorCoefficient b =
      singletonCoefficient 0 (line, .hyperplane) (.inr (SurfaceFirstDescendant.query 2 0 b 0)) := by
  simp only [singletonCoefficient, energy_line, Nat.sub_self, shift_line,
    L24Relation.pointCoefficient, L24Relation.cotangentRelation,
    Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  trans ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.pointCoefficient X (zeroColumn b) (L24Gluing.term j) shifted 0 labels
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [remainderPointCoefficient_eq X (zeroColumn b) (firstCoefficientVertex X 0 b 0)
      (firstCoefficientVertex_eq (X := X) 0 b 0) (L24Gluing.term j) shifted 0 labels]
    change SurfaceGenusTwo.pointCoefficient X (zeroColumn b) _ (0 + shifted) 0 _ = _
    rw [zero_add]
  · apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ((genusTwoFrame_checked j).mp hj).1⟩
    · intro j hj hnot
      have hne : (L24Gluing.term j).expression.maxComponentGenus ≠ 2 := fun h ↦
        hnot ((genusTwoFrame_checked j).mpr ⟨(Finset.mem_filter.mp hj).2, h⟩)
      rw [SurfaceGenusTwo.pointCoefficient, if_neg hne, mul_zero]

private def boundary (s : State X) := SurfaceGenusTwoBlowupBoundary.value s.1 s.2

private theorem earlier_degree_zero (s : State X) (h : Earlier X s state) :
    X.planeDegree s.1 = 0 := by
  rw [earlier_iff] at h
  change X.planeDegree s.1 < X.planeDegree line ∨
    (X.planeDegree s.1 = X.planeDegree line ∧
      (s.2.rank < 0 ∨ (s.2.rank = 0 ∧ X.effective.energy s.1 < X.effective.energy line))) at h
  rw [degree_line, energy_line] at h
  rcases h with h | ⟨hd, h⟩
  · omega
  · have hz : X.effective.energy s.1 = 0 := by omega
    rw [(X.effective.energy_eq_zero_iff s.1).mp hz, map_zero]

private theorem masked (v : State X → ℚ)
    (hv : ∀ s, X.planeDegree s.1 = 0 → v s = boundary s) :
    earlierCandidate state v = boundary := by
  funext s
  unfold earlierCandidate
  by_cases he : Earlier X s state
  · rw [if_pos he]
    exact hv s (earlier_degree_zero s he)
  · rw [if_neg he]
    symm
    apply SurfaceGenusTwoBlowupBoundary.value_of_ne_zero
    intro hz
    apply he
    exact earlier_of_planeDegree_lt X _ _ (by rw [hz, map_zero, degree_line]; decide)

/-- Reduction of the well-founded value to the original lower-genus constant and its
three signed class-zero coefficients. -/
theorem value_eq : SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) =
    SurfaceGenusTwoBlowupScalar.constant 0 (line, .hyperplane) -
      divisorCoefficient .hyperplane / 960 -
      (divisorCoefficient (.exceptional 0) + divisorCoefficient (.exceptional 1)) / 2880 := by
  have hd : 0 < X.planeDegree state.1 := by rw [degree_line]; decide
  have hs := (SurfaceGenusTwoBlowupBoundedCertificate.mem_states X 1 state).mpr
    (show X.effective.energy line ≤ 1 by rw [energy_line])
  have hr := SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row 0 1 state
    (canonicalValuation boundary) hs hd
  have hm := masked_replay_eq_earlier_sum 0 1 state boundary
  rw [masked boundary (fun _ _ ↦ rfl), hr] at hm
  let col (f : Family X) : Variable X := .inr (f.query 0)
  have hc : columns (earlierStates 1 state boundary) =
      {col .hyperplane, col (.exceptional 0), col (.exceptional 1)} := by decide +kernel
  have h₀ : col .hyperplane ∉ ({col (.exceptional 0), col (.exceptional 1)} : Finset _) := by
    decide +kernel
  have h₁ : col (.exceptional 0) ∉ ({col (.exceptional 1)} : Finset _) := by decide +kernel
  rw [hc, Finset.sum_insert h₀, Finset.sum_insert h₁, Finset.sum_singleton] at hm
  have hH : col .hyperplane = zeroColumn .hyperplane := by decide +kernel
  have hE (i : Fin 2) : col (.exceptional i) = zeroColumn (.exceptional i) := by
    fin_cases i <;> decide +kernel
  have coeff (b : SurfaceBasisLabel X) :
      singletonCoefficient 0 state (zeroColumn b) = divisorCoefficient b :=
    (divisorCoefficient_eq b).symm
  simp only [col, canonicalValuation_query, boundary, SurfaceGenusTwoBlowupBoundary.value_zero,
    SurfaceGenusTwoBlowupBoundary.initial] at hm
  change RationalTerms.eval (canonicalValuation boundary)
    (SurfaceGenusTwoBlowupRecursion.row 0 state) = constant 0 state +
      (singletonCoefficient 0 state (col .hyperplane) * (-1 / 960) +
      (singletonCoefficient 0 state (col (.exceptional 0)) * (-1 / 2880) +
       singletonCoefficient 0 state (col (.exceptional 1)) * (-1 / 2880))) at hm
  rw [hH, hE, hE, coeff, coeff, coeff] at hm
  let v := SurfaceGenusTwoBlowupRecursion.values (X := X) 0
  have he := SurfaceGenusTwoBlowupRecursion.values_equations 0 state hd
  rw [eval_row_masked 0 state v hd, masked v
    (fun s h ↦ SurfaceGenusTwoBlowupRecursion.values_boundary 0 s h), hm] at he
  change (-1 : ℚ) * v state + _ = 0 at he
  change v state = _
  linarith only [he]

end AxiomaticGW.BlowupTwoLineH
