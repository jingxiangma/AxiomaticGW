/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupKCoefficients

/-!
# Consumers of the complete exceptional BP coefficient and support APIs

The consumers preserve both exceptional labels and every full curve class.
They check the nonzero pure-exceptional pivot, mixed classes with negative or
zero signed multiplicity, the signed point coefficient, and distinct classes
with equal plane degree and energy. Class zero fails the added-point condition.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupKCoefficients
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupKCoefficients

/-- The first exceptional row never couples to the second exceptional label at
its own full class, including classes with both exceptional coordinates present. -/
theorem other_exceptional_same_class (beta : SurfaceTarget.blowupTwo.Curve)
    (hbeta : 0 < SurfaceTarget.blowupTwo.effective.energy beta) :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo
        (SurfaceTarget.blowupTwo.effective.energy beta - 1) beta 0
        (SurfaceGenusZero.pointLabels ![.exceptional 0, .exceptional 0, .exceptional 0]
          (SurfaceTarget.blowupTwo.effective.energy beta - 1)))
      {Sum.inr (SurfaceFirstDescendant.query 2 beta (.exceptional 1)
        (SurfaceTarget.blowupTwo.effective.energy beta))} = 0 := by
  simpa only [if_neg (show (0 : Fin 2) ≠ 1 by decide)] using
    exceptional_coefficient (X := .blowupTwo) 0 1 beta hbeta

theorem hirzebruchOne_pure_exceptional_pivot :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 0, .exceptional 0, .exceptional 0] 0))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] (.exceptional 0) 1)} = -18 :=
  exceptional_coefficient_self (X := .hirzebruchOne) 0 ![1, 0] (by decide +kernel)

/-- The class 2E+F has signed exceptional multiplicity minus one. Its point
coefficient retains the negative sign, while the exceptional pivot is unchanged. -/
theorem hirzebruchOne_negative_multiplicity_point :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 0, .exceptional 0, .exceptional 0] 3))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1] .point 3)} = -18 := by
  constructor
  · decide +kernel
  · have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 1] = 4 := by decide +kernel
    have ha : SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 := by
      decide +kernel
    have h := point_coefficient (X := .hirzebruchOne) 0 ![2, 1] (by decide +kernel)
    norm_num only [he, ha] at h
    exact h

theorem blowupTwo_mixed_second_exceptional_pivot :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 1, .exceptional 1, .exceptional 1] 5))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1, 3] (.exceptional 1) 6)} = -18 :=
  exceptional_coefficient_self (X := .blowupTwo) 1 ![2, 1, 3] (by decide +kernel)

theorem blowupTwo_mixed_second_point_coefficient :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 1, .exceptional 1, .exceptional 1] 5))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1, 3] .point 5)} = 36 := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![2, 1, 3] = 6 := by decide +kernel
  have ha : SurfaceTarget.blowupTwo.signedMultiplicity ![2, 1, 3] 1 = 2 := by
    decide +kernel
  have h := point_coefficient (X := .blowupTwo) 1 ![2, 1, 3] (by decide +kernel)
  norm_num only [he, ha] at h
  exact h

/-- A zero signed intersection kills the P coefficient without killing K's
constant pivot. This class remains in the full effective domain. -/
theorem blowupTwo_zero_multiplicity_point_and_exceptional :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 0, 1] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 0, .exceptional 0, .exceptional 0] 1))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 1] .point 1)} = 0 ∧
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 1 ![1, 0, 1] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 0, .exceptional 0, .exceptional 0] 1))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0, 1] (.exceptional 0) 2)} = -18 := by
  constructor
  · have he : SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1] = 2 := by decide +kernel
    have ha : SurfaceTarget.blowupTwo.signedMultiplicity ![1, 0, 1] 0 = 0 := by
      decide +kernel
    have h := point_coefficient (X := .blowupTwo) 0 ![1, 0, 1] (by decide +kernel)
    norm_num only [he, ha] at h
    exact h
  · exact exceptional_coefficient_self (X := .blowupTwo) 0 ![1, 0, 1] (by decide +kernel)

/-- The canonical support API excludes a different full exceptional class with
identical degree, rank and energy. No equality of these measures identifies classes. -/
theorem equal_measure_distinct_class_absent :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 0 ![1, 0, 0] 0
        (SurfaceGenusZero.pointLabels ![.exceptional 0, .exceptional 0, .exceptional 0] 0))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1, 0] (.exceptional 0) 1)} = 0 := by
  by_contra hc
  have hs := canonical_coefficient_support (X := .blowupTwo) 0 ![1, 0, 0] ![0, 1, 0]
    (.exceptional 0) (by decide +kernel) hc
  rcases hs with ⟨_, he⟩ | he
  · have hn : (![0, 1, 0] : SurfaceTarget.blowupTwo.Curve) ≠ ![1, 0, 0] := by
      decide +kernel
    exact hn he
  · have hn : ¬ SurfaceGenusTwoBlowupOrder.Earlier .blowupTwo
        (![0, 1, 0], .exceptional 0) (![1, 0, 0], .exceptional 0) := by
      rw [SurfaceGenusTwoBlowupOrder.earlier_iff]
      decide +kernel
    exact hn he

theorem classZero_exceptional_underflow :
    BelorousskiPandharipande.pointCoefficient .hirzebruchOne 0 0
      ![.exceptional 0, .exceptional 0, .exceptional 0]
      (.inr (SurfaceFirstDescendant.query 2 0 (.exceptional 0) 0)) = 0 := by decide +kernel

end AxiomaticGWTest.SurfaceGenusTwoBlowupKCoefficients
