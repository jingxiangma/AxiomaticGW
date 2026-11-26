/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients

/-!
# Consumers of the uniform BP HHH first-descendant coefficients

The examples preserve pure exceptional and mixed full classes, both exceptional
labels, a negative signed multiplicity, and the positive-plane-degree pivot.
The class-zero constructor check excludes a false H coefficient caused by
natural subtraction at energy zero. Larger marking counts use the uniform
proof, rather than replaying their full graph expansion.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupPCoefficients
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupPCoefficients

theorem hirzebruchOne_fiber_point :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 1 ![0, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 1))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![0, 1] .point 1)} = -18 := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 1] = 2 := by decide +kernel
  have hd : SurfaceTarget.hirzebruchOne.planeDegree ![0, 1] = 1 := rfl
  have h := point_coefficient (X := .hirzebruchOne) ![0, 1] (by decide +kernel)
  norm_num only [he, hd] at h
  exact h

theorem hirzebruchOne_exceptional_point :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 0))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] .point 0)} = 0 := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![1, 0] = 1 := by decide +kernel
  have hd : SurfaceTarget.hirzebruchOne.planeDegree ![1, 0] = 0 := rfl
  have h := point_coefficient (X := .hirzebruchOne) ![1, 0] (by decide +kernel)
  norm_num only [he, hd] at h
  exact h

theorem hirzebruchOne_exceptional_hyperplane :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 0 ![1, 0] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 0))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![1, 0] .hyperplane 1)} = 18 :=
  hyperplane_coefficient (X := .hirzebruchOne) ![1, 0] (by decide +kernel)

theorem blowupTwo_mixed_point :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 5))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1, 3] .point 5)} = -54 := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![2, 1, 3] = 6 := by decide +kernel
  have hd : SurfaceTarget.blowupTwo.planeDegree ![2, 1, 3] = 3 := rfl
  have h := point_coefficient (X := .blowupTwo) ![2, 1, 3] (by decide +kernel)
  norm_num only [he, hd] at h
  exact h

theorem blowupTwo_first_exceptional_absent :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 5))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1, 3] (.exceptional 0) 6)} = 0 :=
  exceptional_coefficient (X := .blowupTwo) ![2, 1, 3] 0 (by decide +kernel)

theorem blowupTwo_second_exceptional_absent :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 5))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1, 3] (.exceptional 1) 6)} = 0 :=
  exceptional_coefficient (X := .blowupTwo) ![2, 1, 3] 1 (by decide +kernel)

theorem blowupTwo_mixed_point_pivot :
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .blowupTwo 5 ![2, 1, 3] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 5))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1, 3] .point 5)} ≠ 0 :=
  point_coefficient_ne_zero (X := .blowupTwo) ![2, 1, 3]
    (by decide +kernel) (by decide +kernel)

/-- The class 2E+F has d=1 and signed exceptional multiplicity minus one.
The uniform coefficient uses its full class without truncating that sign. -/
theorem hirzebruchOne_negative_multiplicity_point :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
    RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms .hirzebruchOne 3 ![2, 1] 0
        (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .hyperplane] 3))
      {Sum.inr (SurfaceFirstDescendant.query 2 ![2, 1] .point 3)} = -18 := by
  constructor
  · decide +kernel
  · have he : SurfaceTarget.hirzebruchOne.effective.energy ![2, 1] = 4 := by decide +kernel
    have hd : SurfaceTarget.hirzebruchOne.planeDegree ![2, 1] = 1 := rfl
    have h := point_coefficient (X := .hirzebruchOne) ![2, 1] (by decide +kernel)
    norm_num only [he, hd] at h
    exact h

theorem classZero_hyperplane_underflow :
    BelorousskiPandharipande.pointCoefficient .hirzebruchOne 0 0
      ![.hyperplane, .hyperplane, .hyperplane]
      (.inr (SurfaceFirstDescendant.query 2 0 .hyperplane 0)) = 0 := by decide +kernel

end AxiomaticGWTest.SurfaceGenusTwoBlowupPCoefficients
