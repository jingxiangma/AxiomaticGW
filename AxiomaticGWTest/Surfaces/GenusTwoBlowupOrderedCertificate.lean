/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupOrderedCertificate

/-! Ordered scalar replay skips own/later coefficients while preserving actual equations. -/

@[expose] public section
namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupOrderedCertificate
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
  SurfaceGenusTwoBlowupOrderedCertificate
set_option maxRecDepth 20000

/-- Every symbolic pivot agrees with the compressed complete-row coefficient at its full key. -/
theorem closed_pivot_eq_compressed (X : SurfaceTarget) (i : Fin X.blowups) (s : State X)
    (hd : 0 < X.planeDegree s.1) :
    SurfaceGenusTwoBlowupScalar.singletonCoefficient i s (.inr (s.2.query s.1)) = pivot s := by
  rw [SurfaceGenusTwoBlowupScalar.singletonCoefficient_eq, ← pivot_eq i s hd]

/-- The primary pivot is six times plane degree even at negative signed multiplicity. -/
theorem negative_signed_primary_pivot :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
      pivot (X := .hirzebruchOne) (![2, 1], .primary) = 6 := by
  constructor <;> decide +kernel

/-- Strict-order masking removes its exact own key, including nominal dimension-invalid P0. -/
theorem nominal_point_own_mask_zero (candidate : State .hirzebruchOne → ℚ) :
    earlierCandidate (0, .point) candidate (0, .point) = 0 :=
  earlierCandidate_own_zero _ candidate

/-- A later primary candidate is masked before any singleton coefficient is evaluated. -/
theorem later_nonzero_candidate_masked : earlierCandidate
    (X := .hirzebruchOne) (![0, 1], .point) (fun _ ↦ 7) (![0, 1], .primary) = 0 := by
  decide +kernel

/-- Equal measure does not make another full class an allowed predecessor. -/
theorem equal_measure_collision_masked :
    measure .blowupTwo (![1, 0, 1], .hyperplane) =
      measure .blowupTwo (![0, 1, 1], .hyperplane) ∧
    earlierCandidate (X := .blowupTwo) (![1, 0, 1], .hyperplane)
      (fun _ ↦ 7) (![0, 1, 1], .hyperplane) = 0 := by
  constructor <;> decide +kernel

/-- A foreign exceptional label at the same full class/rank is not an earlier slot. -/
theorem exceptional_label_collision_masked : earlierCandidate
    (X := .blowupTwo) (![0, 0, 1], .exceptional 0) (fun _ ↦ 7)
      (![0, 0, 1], .exceptional 1) = 0 := by
  decide +kernel

/-- An actual earlier H sector with nonzero value is retained, including negative multiplicity. -/
theorem earlier_negative_signed_class_retained :
    (![2, 1], .hyperplane) ∈ earlierStates (X := .hirzebruchOne) 4
      (![2, 1], .primary) (fun _ ↦ 7) := by
  rw [mem_earlierStates, SurfaceGenusTwoBlowupBoundedCertificate.mem_states, earlier_iff]
  decide +kernel

/-- An earlier candidate with value zero does not trigger expensive coefficient replay. -/
theorem earlier_zero_candidate_omitted :
    (![0, 1], .hyperplane) ∉ earlierStates (X := .hirzebruchOne) 2
      (![0, 1], .primary) (fun _ ↦ 0) := by
  rw [mem_earlierStates]
  simp only [ne_eq, not_true_eq_false, and_false, not_false_eq_true]

/-- The producer's earlier nonzero columns and closed pivot describe the complete equation. -/
theorem producer_equation_exact (X : SurfaceTarget) (i : Fin X.blowups) (B : ℕ)
    (candidate : State X → ℚ) (s : State X) : replay i B candidate s =
      SurfaceGenusTwoBlowupScalar.constant i s + pivot s * candidate s +
        ∑ v ∈ SurfaceGenusTwoBlowupScalar.columns (earlierStates B s candidate),
          SurfaceGenusTwoBlowupScalar.singletonCoefficient i s v *
            canonicalValuation candidate v := replay_eq_explicit i B candidate s

/-- The ordered checker preserves the old complete-grid checker on every stored full state. -/
theorem ordered_check_preserves_bounded (X : SurfaceTarget) (i : Fin X.blowups)
    (B : ℕ) (candidate : State X → ℚ) (s : State X)
    (hs : X.effective.energy s.1 ≤ B) :
    checkRow i B candidate s = SurfaceGenusTwoBlowupBoundedCertificate.checkRow i B candidate s :=
  checkRow_eq i B candidate s ((SurfaceGenusTwoBlowupBoundedCertificate.mem_states X B s).mpr hs)

/-- Corrupting the H initial seed remains rejected by the ordered checker. -/
theorem corrupt_h_boundary_rejected : checkRow (X := .hirzebruchOne) 0 0
    (fun _ ↦ 0) (0, .hyperplane) = false := by
  decide +kernel

/-- Ordered table acceptance still identifies each exact full-state reconstructed value. -/
theorem accepted_ordered_table_sound (X : SurfaceTarget) (i : Fin X.blowups) (B : ℕ)
    (candidate : State X → ℚ) (hc : checkTable i B candidate = true)
    (s : State X) (hs : X.effective.energy s.1 ≤ B) :
    candidate s = SurfaceGenusTwoBlowupRecursion.values i s :=
  checkTable_sound i B candidate hc s hs

end AxiomaticGWTest.Surfaces.GenusTwoBlowupOrderedCertificate
