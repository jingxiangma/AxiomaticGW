/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNEEEPrimary

/-! Boundary consumers for the actual shifted exceptional BP primary coefficient. -/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNEEEPrimary
open AxiomaticGW

/-- Extract the primary column from the complete original shifted exceptional BP row. -/
abbrev value (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) : ℚ :=
  RationalTerms.coefficient
    (BelorousskiPandharipande.normalizedGenusTwoTerms X (X.effective.energy beta)
      (beta + X.exceptionalCurve i) 0 (SurfaceGenusZero.pointLabels
        (![.exceptional i, .exceptional i, .exceptional i] : Fin 3 → SurfaceBasisLabel X)
        (X.effective.energy beta)))
    {(.inr (SurfaceQuery.points X 2 beta (X.effective.energy beta + 1)))}

/-- F1 retains a nonzero primary coefficient when the signed exceptional multiplicity is zero. -/
theorem f1_multiplicity_zero : value .hirzebruchOne 0 ![1, 1] = 12 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- The full Bl2P2 class at zero selected multiplicity keeps its other exceptional coordinate. -/
theorem bl2_multiplicity_zero : value .blowupTwo 0 ![1, 0, 1] = 12 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- A reducible F1 class with negative signed multiplicity is included in the formula. -/
theorem f1_negative_multiplicity : value .hirzebruchOne 0 ![2, 1] = 30 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- Positive signed multiplicity gives the original normalized coefficient with its sign. -/
theorem f1_positive_multiplicity : value .hirzebruchOne 0 ![0, 1] = -6 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- Class zero remains covered without an energy positivity premise. -/
theorem f1_zero_class : value .hirzebruchOne 0 0 = 12 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- The selected pure exceptional generator has signed multiplicity minus one. -/
theorem bl2_pure_exceptional : value .blowupTwo 0 ![1, 0, 0] = 30 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- A foreign exceptional generator is distinguished as a full class. -/
theorem bl2_foreign_exceptional : value .blowupTwo 0 ![0, 1, 0] = 12 := by
  rw [value, SurfaceGenusTwoBlowupNEEEPrimary.normalizedCoefficient_primary_shifted]
  norm_num [SurfaceTarget.signedMultiplicity, SurfaceTarget.divisorIntersections,
    SurfaceTarget.latticeCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

end AxiomaticGWTest.SurfaceGenusTwoBlowupNEEEPrimary
