/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPFrame

/-! # The ruling H pivot has only three class-zero descendant columns

At plane degree one all earlier H states have energy at most one and are
already known. The shifted 815-column equation therefore reduces to its
lower-genus constant and the three class-zero divisor seed coefficients.
The shift is always by the first exceptional generator, even on the second ruling.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.H
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction SurfaceGenusTwoBlowupScalar
open SurfaceGenusTwoBlowupOrderedCertificate SurfaceGenusTwoBlowupHUniform SurfaceGenusTwo
open _root_.AxiomaticGW.BlowupTwoLineH (zeroColumn labels)

/-- The requested full class in the first canonical sector. -/
def state (i : Fin 2) : State X := (curve i, .hyperplane)

/-- The shifted source uses two units of exceptional degree in total. -/
def shifted (i : Fin 2) : X.Curve := curve i + X.exceptionalCurve 0

/-- All genus-two diagrams of the full shifted L24 equation at a class-zero divisor column. -/
def divisorCoefficient (i : Fin 2) (b : SurfaceBasisLabel X) : ℚ :=
  ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    remainderPointCoefficient X (zeroColumn b) (firstCoefficientVertex X 0 b 0)
      (L24Gluing.term j) (shifted i) 1 labels

private theorem energy (i : Fin 2) : X.effective.energy (curve i) = 2 := by
  fin_cases i <;> decide +kernel

private theorem degree (i : Fin 2) : X.planeDegree (curve i) = 1 := by
  fin_cases i <;> decide +kernel

/-- Each divisor coefficient belongs to the complete canonical H row. -/
theorem divisorCoefficient_eq (i : Fin 2) (b : SurfaceBasisLabel X) :
    divisorCoefficient i b =
      singletonCoefficient 0 (state i) (.inr (SurfaceFirstDescendant.query 2 0 b 0)) := by
  simp only [state, singletonCoefficient, energy, Nat.reduceSub,
    show curve i + X.exceptionalCurve 0 = shifted i from rfl,
    L24Relation.pointCoefficient, L24Relation.cotangentRelation,
    Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]
  trans ∑ j ∈ genusTwoFrame, L24CorrectionsReplay.fullClaim j *
    SurfaceGenusTwo.pointCoefficient X (zeroColumn b) (L24Gluing.term j) (shifted i) 1 labels
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [remainderPointCoefficient_eq X (zeroColumn b) (firstCoefficientVertex X 0 b 0)
      (firstCoefficientVertex_eq (X := X) 0 b 0) (L24Gluing.term j) (shifted i) 1 labels]
    change SurfaceGenusTwo.pointCoefficient X (zeroColumn b) _ (0 + shifted i) 1 _ = _
    rw [zero_add]
  · apply Finset.sum_subset
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ((genusTwoFrame_checked j).mp hj).1⟩
    · intro j hj hnot
      have hne : (L24Gluing.term j).expression.maxComponentGenus ≠ 2 := fun h ↦
        hnot ((genusTwoFrame_checked j).mpr ⟨(Finset.mem_filter.mp hj).2, h⟩)
      rw [SurfaceGenusTwo.pointCoefficient, if_neg hne, mul_zero]

private def boundary (s : State X) := SurfaceGenusTwoBlowupBoundary.value s.1 s.2

private theorem old (i : Fin 2) (s : State X) (he : Earlier X s (state i)) :
    X.planeDegree s.1 = 0 ∨ X.effective.energy s.1 ≤ 1 := by
  rw [earlier_iff] at he
  change X.planeDegree s.1 < X.planeDegree (curve i) ∨
    (X.planeDegree s.1 = X.planeDegree (curve i) ∧
      (s.2.rank < 0 ∨ (s.2.rank = 0 ∧ X.effective.energy s.1 < X.effective.energy (curve i)))) at he
  rw [degree, energy] at he
  omega

private theorem masked (i : Fin 2) (v : State X → ℚ)
    (hv : ∀ s, Earlier X s (state i) → v s = boundary s) :
    earlierCandidate (state i) v = boundary := by
  funext s
  unfold earlierCandidate
  by_cases he : Earlier X s (state i)
  · rw [if_pos he]
    exact hv s he
  · rw [if_neg he]
    symm
    apply SurfaceGenusTwoBlowupBoundary.value_of_ne_zero
    intro hz
    apply he
    apply earlier_of_planeDegree_lt
    change X.planeDegree s.1 < X.planeDegree (curve i)
    rw [hz, map_zero, degree]
    decide

private theorem actual_old (i : Fin 2) (s : State X) (he : Earlier X s (state i)) :
    SurfaceGenusTwoBlowupRecursion.values 0 s = boundary s := by
  by_cases hd : X.planeDegree s.1 = 0
  · exact SurfaceGenusTwoBlowupRecursion.values_boundary 0 s hd
  · have hb := (old i s he).resolve_left hd
    rw [BlowupTwoLineTable.values_eq s hb, BlowupTwoLineTable.candidate, if_neg hd]
    symm
    apply SurfaceGenusTwoBlowupBoundary.value_of_ne_zero
    intro hz
    exact hd (hz ▸ map_zero _)

/-- Reduction of the well-founded value to the original lower-genus constant and its
three signed class-zero coefficients. -/
theorem value_eq (i : Fin 2) : SurfaceGenusTwoBlowupRecursion.values 0 (state i) =
    SurfaceGenusTwoBlowupScalar.constant 0 (state i) -
      divisorCoefficient i .hyperplane / 960 -
      (divisorCoefficient i (.exceptional 0) + divisorCoefficient i (.exceptional 1)) / 2880 := by
  have hd : 0 < X.planeDegree (state i).1 := by
    change 0 < X.planeDegree (curve i)
    rw [degree]
    decide
  have hs := (SurfaceGenusTwoBlowupBoundedCertificate.mem_states X 2 (state i)).mpr
    (show X.effective.energy (curve i) ≤ 2 by rw [energy])
  have hr := SurfaceGenusTwoBlowupBoundedCertificate.replay_eq_row 0 2 (state i)
    (canonicalValuation boundary) hs hd
  have hm := masked_replay_eq_earlier_sum 0 2 (state i) boundary
  rw [masked i boundary (fun _ _ ↦ rfl), hr] at hm
  let col (f : Family X) : Variable X := .inr (f.query 0)
  have hc : columns (earlierStates 2 (state i) boundary) =
      {col .hyperplane, col (.exceptional 0), col (.exceptional 1)} := by
    fin_cases i <;> decide +kernel
  have h₀ : col .hyperplane ∉ ({col (.exceptional 0), col (.exceptional 1)} : Finset _) := by
    decide +kernel
  have h₁ : col (.exceptional 0) ∉ ({col (.exceptional 1)} : Finset _) := by decide +kernel
  rw [hc, Finset.sum_insert h₀, Finset.sum_insert h₁, Finset.sum_singleton] at hm
  have hH : col .hyperplane = zeroColumn .hyperplane := by decide +kernel
  have hE (i : Fin 2) : col (.exceptional i) = zeroColumn (.exceptional i) := by
    fin_cases i <;> decide +kernel
  have coeff (b : SurfaceBasisLabel X) :
      singletonCoefficient 0 (state i) (zeroColumn b) = divisorCoefficient i b :=
    (divisorCoefficient_eq i b).symm
  simp only [col, canonicalValuation_query, boundary, SurfaceGenusTwoBlowupBoundary.value_zero,
    SurfaceGenusTwoBlowupBoundary.initial] at hm
  change RationalTerms.eval (canonicalValuation boundary)
    (SurfaceGenusTwoBlowupRecursion.row 0 (state i)) = constant 0 (state i) +
      (singletonCoefficient 0 (state i) (col .hyperplane) * (-1 / 960) +
      (singletonCoefficient 0 (state i) (col (.exceptional 0)) * (-1 / 2880) +
       singletonCoefficient 0 (state i) (col (.exceptional 1)) * (-1 / 2880))) at hm
  rw [hH, hE, hE, coeff, coeff, coeff] at hm
  let v := SurfaceGenusTwoBlowupRecursion.values (X := X) 0
  have he := SurfaceGenusTwoBlowupRecursion.values_equations 0 (state i) hd
  rw [eval_row_masked 0 (state i) v hd, masked i v (actual_old i), hm] at he
  change (-1 : ℚ) * v (state i) + _ = 0 at he
  change v (state i) = _
  linarith only [he]

end AxiomaticGW.BlowupTwoRuling.H
