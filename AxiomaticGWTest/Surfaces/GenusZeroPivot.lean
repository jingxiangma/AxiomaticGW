/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusZeroPivot
import AxiomaticGW.Surfaces.PlaneGenusZero

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusZeroPivot

open AxiomaticGW SurfaceGenusZero SurfacePolynomialReduction

/-- Cancellation is collected before extraction, and a repeated variable is nonlinear. -/
example : RationalTerms.coefficient
    (RationalTerms.mul
      (RationalTerms.term 2 {0} + RationalTerms.term (-2) {0} + RationalTerms.term 3 0)
      (RationalTerms.term 5 {0} + RationalTerms.term 7 0 + RationalTerms.term 9 {0, 0}))
    ({0} : Multiset ℕ) = 15 := by decide +kernel

private def threeVertices : GluingExpression 0 ((Fin 1 ⊕ Fin 2) ⊕ Fin 2) :=
  (((GluingExpression.fundamental 0 (Option (Option (Fin 1)))
      (by unfold StableArity; decide)).separating
    (GluingExpression.fundamental 0 (Option (Fin 2))
      (by unfold StableArity; decide))).relabel
        (optionSumEquivLeft (Fin 1) (Fin 2)).symm).separating
    (GluingExpression.fundamental 0 (Option (Fin 2))
      (by unfold StableArity; decide))

/-- The recursive evaluator retains both unit/point node pairings in a three-vertex tree. -/
example : RationalTerms.coefficient
    (threeVertices.surfaceTerms .plane (primaryVertexTerms .plane) ![1] 0
      (fun _ ↦ .hyperplane)) {pointVariable .plane ![1]} = 1 := by
  rw [← pointCoefficientEval_eq _ (by decide +kernel) _ rfl]
  decide +kernel

/-- Equal anticanonical energy does not identify the two exceptional classes. -/
example (p : RationalTerms (Variable .blowupTwo))
    (hp : PointTerms (![1, 0, 0] : SurfaceTarget.blowupTwo.Curve) p) :
    RationalTerms.coefficient p {pointVariable .blowupTwo ![0, 1, 0]} = 0 := by
  apply hp.coefficient_eq_zero_of_curve_ne
  intro he
  have hc := congrFun he 0
  change (0 : ℕ) = 1 at hc
  exact Nat.zero_ne_one hc

/-- A stable four-point degree-zero vertex vanishes for all three targets and all labels. -/
example (X : SurfaceTarget) (a : Fin 4 → SurfaceBasisLabel X) :
    constantCoefficient (GluingExpression.fundamental 0 (Fin 4)
      (by unfold StableArity; decide)) a = 0 :=
  constantCoefficient_fundamental_eq_zero_of_card_ne_three _ _ _ (by decide)

/-- Splitting extra markings across both vertices contributes zero uniformly in the class. -/
example (X : SurfaceTarget) (beta : X.Curve) (hb : beta ≠ 0)
    (a : Fin 3 ⊕ Fin 3 → SurfaceBasisLabel X) :
    pointCoefficient
      ((GluingExpression.fundamental 0 (Option (Fin 3))
        (by unfold StableArity; decide)).separating
        (GluingExpression.fundamental 0 (Option (Fin 3))
          (by unfold StableArity; decide))) beta a = 0 :=
  pointCoefficient_separating_fundamental_eq_zero _ _ _ _ (by decide) (by decide) beta hb a

/-- The conic pivot is certified against the full request, with both additional markings. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .plane 2 ![2] 0 SurfacePlaneGenusZero.conicLabels)
    {pointVariable .plane ![2]} = 1 := by
  rw [← WDVV.primaryPointCoefficient_eq _ _ _ (by decide +kernel)]
  decide +kernel

/-- The classical exceptional self-intersection retains its negative sign on F₁. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .hirzebruchOne 0 ![1, 1] 0
      ![.hyperplane, .point, .exceptional 0, .exceptional 0])
    {pointVariable .hirzebruchOne ![1, 1]} = -1 := by
  rw [← WDVV.primaryPointCoefficient_eq _ _ _ (by decide +kernel)]
  decide +kernel

/-- A positive plane-degree branch on the two-point blowup, including added point labels. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .blowupTwo 2 ![2, 1, 2] 0
      (Option.elim · .point (Option.elim · .point
        ![.hyperplane, .point, .exceptional 0, .exceptional 0])))
    {pointVariable .blowupTwo ![2, 1, 2]} = -2 := by
  rw [← WDVV.primaryPointCoefficient_eq _ _ _ (by decide +kernel)]
  decide +kernel

/-- The zero-plane-degree branch uses the actual nonzero exceptional coordinate. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .blowupTwo 0 ![0, 3, 0] 0
      ![.hyperplane, .hyperplane, .point, .exceptional 1])
    {pointVariable .blowupTwo ![0, 3, 0]} = -3 := by
  rw [← WDVV.primaryPointCoefficient_eq _ _ _ (by decide +kernel)]
  decide +kernel

/-- Choosing the other, zero exceptional coordinate must not certify a nonzero pivot. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .blowupTwo 0 ![0, 3, 0] 0
      ![.hyperplane, .hyperplane, .point, .exceptional 0])
    {pointVariable .blowupTwo ![0, 3, 0]} = 0 := by
  rw [← WDVV.primaryPointCoefficient_eq _ _ _ (by decide +kernel)]
  decide +kernel

/-- A missing point marking fails the dimension condition rather than retaining the conic pivot. -/
example : RationalTerms.coefficient
    (WDVV.primaryTerms .plane 1 ![2] 0
      (Option.elim · .point ![.hyperplane, .hyperplane, .point, .point]))
    {pointVariable .plane ![2]} = 0 := by
  rw [← WDVV.primaryPointCoefficient_eq _ _ _ (by decide +kernel)]
  decide +kernel

end AxiomaticGWTest.Surfaces.GenusZeroPivot
