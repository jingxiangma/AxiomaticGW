/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCertificate

/-! Full-state enumeration and scalar replay preserve signed and colliding boundary classes. -/

@[expose] public section
namespace AxiomaticGWTest.Surfaces.GenusTwoBlowupBoundedCertificate
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
  SurfaceGenusTwoBlowupBoundedCertificate

-- No consumer computes a positive-plane reconstructed value.
set_option maxRecDepth 20000

/-- The list is certified against the established complete effective-class bounded set. -/
theorem complete_class_enumeration (X : SurfaceTarget) (B : ℕ) :
    (classes X B).toFinset = X.bounded B := classes_toFinset X B

/-- Reducible F1 classes with negative reconstruction multiplicity are retained. -/
theorem negative_signed_f1_class_retained :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
      (![2, 1], .primary) ∈ states .hirzebruchOne 4 := by
  constructor
  · decide +kernel
  · rw [mem_states]
    decide +kernel

/-- Bl2 classes with one positive and one negative reconstruction multiplicity are retained. -/
theorem mixed_signed_bl2_class_retained :
    SurfaceTarget.blowupTwo.signedMultiplicity ![2, 0, 1] 0 = -1 ∧
      SurfaceTarget.blowupTwo.signedMultiplicity ![2, 0, 1] 1 = 1 ∧
        (![2, 0, 1], .exceptional 1) ∈ states .blowupTwo 3 := by
  constructor
  · decide +kernel
  · constructor
    · decide +kernel
    · rw [mem_states]
      decide +kernel

/-- Equal plane/rank/energy measures do not discard either distinct full class. -/
theorem equal_measure_full_classes_both_retained :
    measure .blowupTwo (![1, 0, 1], .hyperplane) =
      measure .blowupTwo (![0, 1, 1], .hyperplane) ∧
    (![1, 0, 1], .hyperplane) ∈ states .blowupTwo 2 ∧
    (![0, 1, 1], .hyperplane) ∈ states .blowupTwo 2 := by
  constructor
  · decide +kernel
  · constructor <;> rw [mem_states] <;> decide +kernel

/-- The two exceptional sectors at the same full class are both represented. -/
theorem distinct_exceptional_labels_retained :
    (![0, 0, 1], .exceptional 0) ∈ states .blowupTwo 1 ∧
    (![0, 0, 1], .exceptional 1) ∈ states .blowupTwo 1 := by
  constructor <;> rw [mem_states] <;> decide +kernel

/-- Nominal P0 is a complete internal state, while its query stays dimension incompatible. -/
theorem nominal_point_zero_internal :
    ((0, .point) : State .hirzebruchOne) ∈ states .hirzebruchOne 0 ∧
    ¬ ((Family.point : Family .hirzebruchOne).query 0).DimensionCompatible := by
  constructor
  · rw [mem_states]
    simpa only [map_zero] using (Nat.le_refl 0)
  · decide +kernel

/-- Every used row of a bounded grid has exact full-query closure in the original order. -/
theorem bounded_grid_closed (X : SurfaceTarget) (i : Fin X.blowups) (B : ℕ)
    (s : State X) (hs : X.effective.energy s.1 ≤ B) (hd : 0 < X.planeDegree s.1) :
    SurfaceGenusTwoBlowupCertificate.checkClosure i (states X B) s = true :=
  checkClosure_states i B s ((mem_states X B s).mpr hs) hd

/-- Scalar replay retains the complete original selected row, not only its own pivot. -/
theorem exact_scalar_row_replay (X : SurfaceTarget) (i : Fin X.blowups) (B : ℕ)
    (s : State X) (values : Variable X → ℚ)
    (hs : X.effective.energy s.1 ≤ B) (hd : 0 < X.planeDegree s.1) :
    SurfaceGenusTwoBlowupScalar.replay i s values (states X B) =
      RationalTerms.eval values (SurfaceGenusTwoBlowupRecursion.row i s) :=
  replay_eq_row i B s values ((mem_states X B s).mpr hs) hd

/-- No complete polynomial-row construction is needed by the scalar boundary check. -/
theorem boundary_grid_zero_accepted : checkTable (X := .hirzebruchOne) 0 0
    (fun s ↦ SurfaceGenusTwoBlowupBoundary.value s.1 s.2) = true := by
  decide +kernel

/-- The scalar checker refuses a corrupted original H boundary seed. -/
theorem corrupt_h_boundary_rejected : checkRow (X := .hirzebruchOne) 0 0
    (fun _ ↦ 0) (0, .hyperplane) = false := by
  decide +kernel

/-- Scalar acceptance is a certificate for the original well-founded values at every stored key. -/
theorem accepted_scalar_table_sound (X : SurfaceTarget) (i : Fin X.blowups)
    (B : ℕ) (candidate : State X → ℚ) (hc : checkTable i B candidate = true)
    (s : State X) (hs : X.effective.energy s.1 ≤ B) :
    candidate s = SurfaceGenusTwoBlowupRecursion.values i s :=
  checkTable_sound i B candidate hc s hs

end AxiomaticGWTest.Surfaces.GenusTwoBlowupBoundedCertificate
