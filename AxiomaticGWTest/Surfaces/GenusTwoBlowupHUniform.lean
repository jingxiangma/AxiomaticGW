/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHUniform

/-!
# Exact shifted-H frame and effective-remainder regressions

The public identities apply to arbitrary full effective classes. A previously
proved fiber pivot tests the compact API. A different exceptional remainder
tests exact positive-plane-degree source binding. These tests do not replace
a uniform pivot or full support theorem.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHUniform
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupHPivots
  SurfaceGenusTwoBlowupHUniform

set_option maxRecDepth 20000

example (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} =
      firstPsiCoefficient X i beta (X.exceptionalCurve i) :=
  row_coefficient_eq_firstPsi X i beta

example (X : SurfaceTarget) (i : Fin X.blowups) (beta delta : X.Curve) :
    remainderCoefficient X i beta delta =
      L24Relation.pointCoefficient X (pointCount X beta) (beta + delta)
        (labels X i) (hColumn X beta) :=
  remainderCoefficient_eq X i beta delta

/-- The formula retains the zero-energy request, whose physical marking count
is not justified by the positive-energy dimension theorem. -/
example : coefficient .hirzebruchOne 0 0 =
    remainderCoefficient .hirzebruchOne 0 0 (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) :=
  coefficient_eq_remainder .hirzebruchOne 0 0

/-- The compact API preserves the previously checked fiber-class coefficient. -/
example : remainderCoefficient .hirzebruchOne 0 ![0, 1]
    (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) = -1 := by
  rw [← coefficient_eq_remainder]
  exact hirzebruchOne_fiber

/-- The full class `E₁ + L` at source `E₁ + E₂ + L` has the same plane degree
and energy as `E₂ + L`. The compact formula keeps its different remainder `E₂`. -/
example : firstPsiCoefficient .blowupTwo 0 ![1, 0, 1] ![0, 1, 0] =
    L24Relation.pointCoefficient .blowupTwo 1 ![1, 1, 1]
      (labels .blowupTwo 0) (hColumn .blowupTwo ![1, 0, 1]) := by
  rw [← remainderCoefficient_eq_firstPsi, remainderCoefficient_eq]
  congr 1
  decide +kernel

/-- The positive-energy pruning preserves a completely arbitrary effective remainder. -/
example (X : SurfaceTarget) (i : Fin X.blowups) (beta delta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    twoMarkingCoefficient X i beta delta =
      L24Relation.pointCoefficient X (pointCount X beta) (beta + delta)
        (labels X i) (hColumn X beta) := by
  rw [← firstPsiCoefficient_eq_twoMarking_of_pos X i beta delta hbeta,
    ← remainderCoefficient_eq_firstPsi, remainderCoefficient_eq]

/-- Class zero cannot satisfy the premise of the twelve-term pruning. The earlier
unconditional coefficient regression still covers that request. -/
example (X : SurfaceTarget) : ¬0 < X.effective.energy (0 : X.Curve) := by
  rw [map_zero]
  exact Nat.not_lt_zero _

end AxiomaticGWTest.SurfaceGenusTwoBlowupHUniform
