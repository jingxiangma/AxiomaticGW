/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPSupport

/-!
# Consumers of the BP HHH nonprimary support theorem

Equal plane degree does not identify full exceptional coordinates. These
examples cover effective, incomparable and negative-multiplicity requests.
In particular, a smaller-energy K column is later than the P sector in the
proposed order, but its actual full-row coefficient is zero.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupPSupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupPSupport

theorem hirzebruchOne_smaller_energy_exceptional :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 2 ![1, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 2))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1] (.exceptional 0) 2)} = 0 :=
  exceptional_coefficient_eq_zero_of_planeDegree_ge (X := .hirzebruchOne)
    ![1, 1] ![0, 1] 0 (by decide +kernel) le_rfl

/-- Its lower energy does not make the K column earlier than the P sector. -/
theorem hirzebruchOne_smaller_energy_exceptional_order :
    SurfaceTarget.hirzebruchOne.effective.energy ![0, 1] <
        SurfaceTarget.hirzebruchOne.effective.energy ![1, 1] ∧
      ¬SurfaceGenusTwoBlowupOrder.Earlier .hirzebruchOne
        (![0, 1], .exceptional 0) (![1, 1], .point) := by
  constructor
  · decide +kernel
  · rw [SurfaceGenusTwoBlowupOrder.earlier_iff]
    decide +kernel

theorem hirzebruchOne_multiple_exceptional_complement :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1] .hyperplane 2)} = 0 := by
  apply nonprimary_coefficient_eq_zero_of_same_planeDegree (X := .hirzebruchOne)
  · exact fun gamma m ↦ SurfaceFirstDescendant.query_ne_points ![0, 1] gamma .hyperplane 2 m
  · decide +kernel
  · rfl

theorem hirzebruchOne_negative_multiplicity_source :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1] .point 1)} = 0 := by
  constructor
  · decide +kernel
  · apply nonprimary_coefficient_eq_zero_of_same_planeDegree (X := .hirzebruchOne)
    · exact fun gamma m ↦ SurfaceFirstDescendant.query_ne_points ![0, 1] gamma .point 1 m
    · decide +kernel
    · rfl

theorem blowupTwo_mixed_exceptional_complement_first :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 6 ![2, 3, 2] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 6))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 2] (.exceptional 0) 3)} = 0 :=
  exceptional_coefficient_eq_zero_of_planeDegree_ge (X := .blowupTwo)
    ![2, 3, 2] ![1, 0, 2] 0 (by decide +kernel) le_rfl

theorem blowupTwo_mixed_exceptional_complement_second :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 6 ![2, 3, 2] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 6))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 2] (.exceptional 1) 3)} = 0 :=
  exceptional_coefficient_eq_zero_of_planeDegree_ge (X := .blowupTwo)
    ![2, 3, 2] ![1, 0, 2] 1 (by decide +kernel) le_rfl

theorem blowupTwo_incomparable_same_planeDegree :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 0, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1, 1] (.exceptional 1) 2)} = 0 :=
  exceptional_coefficient_eq_zero_of_planeDegree_ge (X := .blowupTwo)
    ![1, 0, 1] ![0, 1, 1] 1 (by decide +kernel) le_rfl

theorem blowupTwo_pure_exceptional_complement :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 1, 0] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 0] (.exceptional 0) 1)} = 0 :=
  exceptional_coefficient_eq_zero_of_planeDegree_ge (X := .blowupTwo)
    ![1, 1, 0] ![1, 0, 0] 0 (by decide +kernel) le_rfl

theorem blowupTwo_higher_planeDegree_excluded :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 0, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 0, 2] (.exceptional 0) 2)} = 0 :=
  exceptional_coefficient_eq_zero_of_planeDegree_ge (X := .blowupTwo)
    ![1, 0, 1] ![0, 0, 2] 0 (by decide +kernel) (by decide +kernel)

/-- The conclusion for a surviving K coefficient is strict plane-degree decrease. -/
theorem exceptional_dependency_decreases_planeDegree {X : SurfaceTarget}
    (beta gamma : X.Curve) (i : Fin X.blowups) (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta - 1)
        beta 0 (SurfaceGenusZero.pointLabels
          (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
          (X.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional i)
        (X.effective.energy gamma))} ≠ 0) :
    X.planeDegree gamma < X.planeDegree beta :=
  exceptional_coefficient_support beta gamma i hbeta hc

/-- Independent kernel replay of the smallest nontrivial exceptional complement. -/
theorem hirzebruchOne_exceptional_complement_direct :
    BelorousskiPandharipande.pointCoefficient .hirzebruchOne 0 ![1, 0]
      ![.hyperplane, .hyperplane, .hyperplane]
      (.inr (SurfaceFirstDescendant.query 2 0 (.exceptional 0) 0)) = 0 := by
  decide +kernel

end AxiomaticGWTest.SurfaceGenusTwoBlowupPSupport
