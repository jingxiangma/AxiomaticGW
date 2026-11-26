/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPPrimarySupport

/-!
# Consumers of full BP HHH primary and canonical support

Smaller energy at equal plane degree is insufficient to precede the P sector
when the requested family is N. The complete original coefficient vanishes,
including multiple and mixed exceptional complements, negative signed
multiplicities, incomparable classes and the degree-zero boundary. A small
independent full-row computation checks the constructor binding.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupPPrimarySupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo
open SurfaceGenusTwoBlowupPPrimarySupport

theorem hirzebruchOne_smaller_energy_primary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![0, 1] 3)} = 0 :=
  primary_coefficient_eq_zero_of_same_planeDegree (X := .hirzebruchOne) ![2, 1] ![0, 1] rfl 3 3

/-- An N column of smaller energy is still later than P at the same plane degree. -/
theorem hirzebruchOne_smaller_energy_primary_order :
    SurfaceTarget.hirzebruchOne.effective.energy ![0, 1] <
        SurfaceTarget.hirzebruchOne.effective.energy ![2, 1] ∧
      ¬SurfaceGenusTwoBlowupOrder.Earlier .hirzebruchOne
        (![0, 1], .primary) (![2, 1], .point) := by
  constructor
  · decide +kernel
  · rw [SurfaceGenusTwoBlowupOrder.earlier_iff]
    decide +kernel

theorem hirzebruchOne_negative_multiplicity_source :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
      RationalTerms.coefficient
        (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
          (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
        {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 ![0, 1] 3)} = 0 := by
  constructor
  · decide +kernel
  · exact hirzebruchOne_smaller_energy_primary

theorem blowupTwo_mixed_exceptional_complement :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 6 ![2, 3, 2] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 6))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2 ![1, 0, 2] 4)} = 0 :=
  primary_coefficient_eq_zero_of_same_planeDegree (X := .blowupTwo) ![2, 3, 2] ![1, 0, 2] rfl 4 6

theorem blowupTwo_incomparable_same_planeDegree :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 0, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2 ![0, 1, 1] 3)} = 0 :=
  primary_coefficient_eq_zero_of_same_planeDegree (X := .blowupTwo) ![1, 0, 1] ![0, 1, 1] rfl 3 1

theorem blowupTwo_higher_planeDegree_excluded :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 0, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2 ![0, 0, 2] 3)} = 0 :=
  primary_coefficient_eq_zero_of_planeDegree_ge (X := .blowupTwo) ![1, 0, 1] ![0, 0, 2]
    (by decide +kernel) 3 1

theorem zero_class_primary_boundary :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 0 0 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 0))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 0 1)} = 0 :=
  primary_coefficient_eq_zero_of_same_planeDegree (X := .hirzebruchOne) 0 0 rfl 1 0

/-- Independently reduce the original normalized constructor at its smallest
positive exceptional class, without using the support theorem. -/
theorem hirzebruchOne_exceptional_full_row_independent :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 0))
      {Sum.inr (SurfaceQuery.points .hirzebruchOne 2 0 1)} = 0 := by
  decide +kernel

theorem blowupTwo_point_calibration_large_exceptional :
    SurfaceDescendant.firstCalibrationMatrix .blowupTwo ![3, 4, 0] (.exceptional 1) .point = 0 :=
  firstCalibrationMatrix_point_eq_zero (X := .blowupTwo) ![3, 4, 0] rfl (.exceptional 1)

/-- Both actual main psi positions retain no same-plane primary coefficient,
even when the point-containing cotangent correction has a large mixed class. -/
theorem blowupTwo_main_pair_point_psi :
    let v : Variable .blowupTwo := .inr (SurfaceQuery.points .blowupTwo 2 ![0, 0, 1] 2)
    remainderVertex .blowupTwo v (coefficientVertex .blowupTwo v) 3 2 (Fin 2)
      (by norm_num [StableArity]) (Pi.single 1 1) inferInstance ![3, 4, 0]
      ![.hyperplane, .point] = 0 :=
  pair_main_primary_zero_of_planeDegree_zero (X := .blowupTwo) ![0, 0, 1] 2 ![3, 4, 0] rfl 3 1

/-- A surviving canonical column is the own P request or decreases the proved order. -/
theorem canonical_dependency_is_own_point_or_earlier {X : SurfaceTarget}
    (beta gamma : X.Curve) (family : SurfaceGenusTwoBlowupOrder.Family X)
    (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (family.query gamma)} ≠ 0) :
    (family = .point ∧ gamma = beta) ∨
      SurfaceGenusTwoBlowupOrder.Earlier X (gamma, family) (beta, .point) :=
  canonical_coefficient_support beta gamma family hbeta hc

/-- In particular a surviving canonical N column must lower the outer plane degree. -/
theorem primary_dependency_decreases_planeDegree {X : SurfaceTarget}
    (beta gamma : X.Curve)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceQuery.points X 2 gamma (X.effective.energy gamma + 1))} ≠ 0) :
    X.planeDegree gamma < X.planeDegree beta :=
  primary_coefficient_support beta gamma _ _ hc

end AxiomaticGWTest.SurfaceGenusTwoBlowupPPrimarySupport
