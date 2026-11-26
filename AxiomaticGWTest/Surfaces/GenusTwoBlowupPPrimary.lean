/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimary

/-!
# Same-class primary coefficients of the complete BP HHH row

These consumers include pure and mixed exceptional classes, negative signed
multiplicity, and positive plane degree. The final regression retains a
nonzero smaller-class primary calibration coefficient: the same-class theorem
does not authorize discarding the rest of the normalized row.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupPPrimary
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupPPrimary

theorem hirzebruchOne_exceptional_primary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 0))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![1, 0] 2)} = 0 :=
  normalized_primary_at_requested_class (X := .hirzebruchOne) ![1, 0] 2 0

theorem hirzebruchOne_fiber_primary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 1 ![0, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![0, 1] 3)} = 0 :=
  normalized_primary_at_requested_class (X := .hirzebruchOne) ![0, 1] 3 1

theorem blowupTwo_mixed_primary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 5))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2 ![2, 1, 3] 7)} = 0 :=
  normalized_primary_at_requested_class (X := .blowupTwo) ![2, 1, 3] 7 5

theorem blowupTwo_multiple_exceptional_primary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 4 ![2, 3, 0] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 4))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2 ![2, 3, 0] 6)} = 0 :=
  normalized_primary_at_requested_class (X := .blowupTwo) ![2, 3, 0] 6 4

theorem hirzebruchOne_negative_multiplicity_primary :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![2, 1] 5)} = 0 := by
  refine ⟨by decide +kernel,
    normalized_primary_at_requested_class (X := .hirzebruchOne) ![2, 1] 5 3⟩

theorem plane_primary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .plane 2 ![1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 2))
      {Sum.inr (SurfaceQuery.points .plane 2 ![1] 4)} = 0 :=
  normalized_primary_at_requested_class (X := .plane) ![1] 4 2

theorem positive_energy_marking_condition {X : SurfaceTarget} (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    X.effective.energy beta = (X.effective.energy beta - 1) + 1 :=
  (canonical_primary_row beta hbeta).1

theorem classZero_marking_condition_excluded {X : SurfaceTarget} :
    ¬X.effective.energy (0 : X.Curve) = (X.effective.energy 0 - 1) + 1 := by
  rw [map_zero]
  omega

/-- A direct constructor check at the smallest positive-energy BP row. -/
theorem exceptional_direct_constructor :
    BelorousskiPandharipande.pointCoefficient .hirzebruchOne 0 ![1, 0]
      ![.hyperplane, .hyperplane, .hyperplane]
      (.inr (SurfaceQuery.points .hirzebruchOne 2 ![1, 0] 2)) = 0 := by
  decide +kernel

/-- Smaller-class primary coefficients remain in the full normalizer. -/
theorem smaller_class_primary_calibration_retained :
    RationalTerms.coefficient (normalizedTerms
      (SurfaceAncestorKey.ofLabels 2 (Fin 4) (by unfold StableArity; omega)
        (![1, 1] : SurfaceTarget.hirzebruchOne.Curve)
        ![1, 0, 0, 0] ![.exceptional 0, .point, .point, .point]))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![0, 1] 3)} = 1 := by
  decide +kernel

theorem multiple_exceptional_hyperplane_calibration
    (row : SurfaceBasisLabel .blowupTwo) :
    SurfaceDescendant.firstCalibrationMatrix .blowupTwo ![2, 3, 0] row .hyperplane = 0 :=
  firstCalibrationMatrix_hyperplane_eq_zero (X := .blowupTwo) ![2, 3, 0] rfl row

theorem classZero_hyperplane_calibration {X : SurfaceTarget} (row : SurfaceBasisLabel X) :
    SurfaceDescendant.firstCalibrationMatrix X 0 row .hyperplane = 0 :=
  firstCalibrationMatrix_hyperplane_eq_zero 0 (map_zero _) row

/-- The H input removes the same-plane smaller-class primary calibration tail.
The preceding exceptional input regression still has coefficient one. -/
theorem same_plane_hyperplane_primary_calibration_absent :
    RationalTerms.coefficient (normalizedTerms
      (SurfaceAncestorKey.ofLabels 2 (Fin 4) (by unfold StableArity; omega)
        (![1, 1] : SurfaceTarget.hirzebruchOne.Curve)
        ![1, 0, 0, 0] ![.hyperplane, .point, .point, .point]))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![0, 1] 3)} = 0 := by
  let q : SurfaceAncestorKey .hirzebruchOne := SurfaceAncestorKey.ofLabels
    2 (Fin 4) (by unfold StableArity; omega) ![1, 1]
    ![1, 0, 0, 0] ![.hyperplane, .point, .point, .point]
  have h : 2 ≤ q.genus ∧ q.totalPsi = 1 := by decide +kernel
  have hh : (q.onePsiInsertion h.2).label = .hyperplane := by decide +kernel +revert
  rw [coefficient_normalizedTerms_hyperplane_same_planeDegree q _ h hh rfl]
  exact coefficient_directNormalizedTerms_eq_zero q le_rfl _ (by decide)

end AxiomaticGWTest.SurfaceGenusTwoBlowupPPrimary
