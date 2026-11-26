/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNForeignSupport

/-! Full-class foreign N support and the retained exceptional calibration seed. -/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNForeignSupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo
open SurfaceGenusTwoBlowupNForeignSupport SurfaceGenusTwoBlowupNEEEPrimary

/-- Arbitrary primary point counts retain the exact full-class foreign cancellation. -/
theorem primary_foreign (X : SurfaceTarget) (i j : Fin X.blowups) (hij : i ≠ j)
    (beta gamma : X.Curve) (hs : gamma + X.exceptionalCurve j = beta + X.exceptionalCurve i)
    (m : ℕ) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (SurfaceQuery.points X 2 gamma m)} = 0 := by
  exact row_foreign_primary_coefficient_zero i j hij beta gamma hs m

/-- The actual graph mechanism also excludes foreign exceptional descendants. -/
theorem exceptional_foreign (X : SurfaceTarget) (i j k : Fin X.blowups) (hij : i ≠ j)
    (beta gamma : X.Curve) (hs : gamma + X.exceptionalCurve j = beta + X.exceptionalCurve i)
    (m : ℕ) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional k) m)} = 0 := by
  exact row_foreign_coefficient_zero i j hij beta _ hs

/-- A degree-two pair of distinct effective full classes has zero foreign N coefficient. -/
theorem degree_two_foreign :
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0 (![0,1,2] : SurfaceTarget.blowupTwo.Curve))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2
        (![1,0,2] : SurfaceTarget.blowupTwo.Curve) 4)} = 0 := by
  apply row_foreign_primary_coefficient_zero 0 1 (by decide) _ _
  · decide +kernel

/-- The other exceptional coordinate gives the reverse full-class cancellation. -/
theorem degree_two_reverse_foreign :
    (![0,1,2] : SurfaceTarget.blowupTwo.Curve) ≠ ![1,0,2] ∧
    RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 1 (![1,0,2] : SurfaceTarget.blowupTwo.Curve))
      {Sum.inr (SurfaceQuery.points .blowupTwo 2
        (![0,1,2] : SurfaceTarget.blowupTwo.Curve) 4)} = 0 := by
  constructor
  · decide +kernel
  · apply row_foreign_primary_coefficient_zero 1 0 (by decide) _ _
    decide +kernel

/-- Foreign calibration input is zero while the own-generator calibration seed remains minus one. -/
theorem calibration_own_and_foreign (X : SurfaceTarget) (i j : Fin X.blowups) (hij : i ≠ j) :
    SurfaceDescendant.firstCalibrationMatrix X (X.exceptionalCurve j) (.exceptional j)
      (.exceptional i) = 0 ∧
    SurfaceDescendant.firstCalibrationMatrix X (X.exceptionalCurve j) (.exceptional j)
      (.exceptional j) = -1 := by
  constructor
  · rw [firstCalibrationMatrix_exceptional_eq]
    rw [SurfaceFirstCalibration.exceptionalMatrix, if_neg]
    intro h
    exact hij (SurfaceBasisLabel.exceptional.inj h.2)
  · rw [firstCalibrationMatrix_exceptional_column, if_pos rfl]

end AxiomaticGWTest.SurfaceGenusTwoBlowupNForeignSupport
