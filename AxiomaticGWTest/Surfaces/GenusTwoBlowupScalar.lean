/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupScalar

/-! Scalar row replay retains signed full classes, labels, source shifts and exact weights. -/

set_option linter.privateModule false

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupScalar
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupScalar

-- Concrete H dispatch uses the unchanged finite L24 source.
set_option maxRecDepth 20000

/-- Negative signed multiplicities do not change the H source shift or added-point count. -/
theorem negative_multiplicity_h_constant :
    constant (X := .blowupTwo) 0 (![2, 3, 1], .hyperplane) =
      L24Relation.pointConstant .blowupTwo 5 ![3, 3, 1]
        ![.hyperplane, .exceptional 0, .exceptional 0, .exceptional 0] := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![2, 3, 1] = 6 := by decide +kernel
  have hs : (![2, 3, 1] : SurfaceTarget.blowupTwo.Curve) +
      SurfaceTarget.blowupTwo.exceptionalCurve 0 = ![3, 3, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [constant, he, hs, Nat.reduceSub, L24Relation.pointConstantGuarded_eq]

/-- The selected four-row N constant preserves all exact weights and its full shifted class. -/
theorem shifted_primary_constant_weights :
    constant (X := .blowupTwo) 1 (![1, 0, 1], .primary) =
      (3 / 2) * BelorousskiPandharipande.pointConstant .blowupTwo 2 ![1, 1, 1]
        ![.exceptional 1, .hyperplane, .hyperplane] +
      (-1) * BelorousskiPandharipande.pointConstant .blowupTwo 2 ![1, 1, 1]
        ![.exceptional 1, .exceptional 1, .hyperplane] +
      (1 / 2) * BelorousskiPandharipande.pointConstant .blowupTwo 2 ![1, 1, 1]
        ![.exceptional 1, .exceptional 1, .exceptional 1] +
      (-1 / 3) * BelorousskiPandharipande.pointConstant .blowupTwo 2 ![1, 1, 1]
        ![.hyperplane, .hyperplane, .hyperplane] := by
  have he : SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1] = 2 := by decide +kernel
  have hd : SurfaceTarget.blowupTwo.planeDegree ![1, 0, 1] = 1 := rfl
  have hs : (![1, 0, 1] : SurfaceTarget.blowupTwo.Curve) +
      SurfaceTarget.blowupTwo.exceptionalCurve 1 = ![1, 1, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [constant, he, hd, hs, Nat.cast_one, mul_one]

/-- The compressed P coefficient retains the proved pivot at a negative-multiplicity class. -/
theorem negative_multiplicity_p_coefficient :
    singletonCoefficient (X := .blowupTwo) 0 (![2, 3, 1], .point)
      (.inr (Family.point.query ![2, 3, 1])) = -18 := by
  have h (beta : SurfaceTarget.blowupTwo.Curve)
      (he : 0 < SurfaceTarget.blowupTwo.effective.energy beta) :
      singletonCoefficient (X := .blowupTwo) 0 (beta, .point)
        (.inr (Family.point.query beta)) = -18 *
          (SurfaceTarget.blowupTwo.planeDegree beta : ℚ) := by
    rw [singletonCoefficient_eq]
    exact SurfaceGenusTwoBlowupPCoefficients.point_coefficient beta he
  have hd : SurfaceTarget.blowupTwo.planeDegree ![2, 3, 1] = 1 := rfl
  exact (h ![2, 3, 1] (by decide +kernel)).trans (by rw [hd]; norm_num)

/-- Distinct same-class exceptional labels remain separate in scalar replay. -/
theorem foreign_exceptional_coefficient :
    singletonCoefficient (X := .blowupTwo) 0 (![2, 3, 1], .exceptional 0)
      (.inr ((Family.exceptional 1).query ![2, 3, 1])) = 0 := by
  have h (beta : SurfaceTarget.blowupTwo.Curve)
      (he : 0 < SurfaceTarget.blowupTwo.effective.energy beta) :
      singletonCoefficient (X := .blowupTwo) 0 (beta, .exceptional 0)
        (.inr ((Family.exceptional 1).query beta)) = 0 := by
    rw [singletonCoefficient_eq]
    exact (SurfaceGenusTwoBlowupKCoefficients.exceptional_coefficient 0 1 beta he).trans
      (if_neg (by decide +kernel))
  exact h ![2, 3, 1] (by decide +kernel)

/-- The full four-row primary pivot is obtained without an alpha-positive restriction. -/
theorem zero_multiplicity_n_coefficient :
    singletonCoefficient (X := .blowupTwo) 0 (![1, 0, 1], .primary)
      (.inr (Family.primary.query ![1, 0, 1])) = 6 := by
  have h (beta : SurfaceTarget.blowupTwo.Curve) :
      singletonCoefficient (X := .blowupTwo) 0 (beta, .primary)
        (.inr (Family.primary.query beta)) = 6 *
          (SurfaceTarget.blowupTwo.planeDegree beta : ℚ) := by
    rw [singletonCoefficient_eq]
    exact SurfaceGenusTwoBlowupNCoefficients.row_primary_coefficient 0 beta
  have hd : SurfaceTarget.blowupTwo.planeDegree ![1, 0, 1] = 1 := rfl
  exact (h ![1, 0, 1]).trans (by rw [hd]; norm_num)

/-- Equal energy and family rank do not identify distinct full classes; repeats are deduplicated. -/
theorem equal_measure_columns_distinct :
    (columns (X := .blowupTwo)
      [(![1, 0, 1], .hyperplane), (![1, 0, 1], .hyperplane),
        (![0, 1, 1], .hyperplane)]).card = 2 := by
  decide +kernel

/-- Zero-valued columns need no coefficient evaluation, but the complete row constant remains. -/
theorem zero_valuation_replay {X : SurfaceTarget} (i : Fin X.blowups) (s : State X)
    (states : List (State X)) :
    replay i s (fun _ ↦ 0) states = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (SurfaceGenusTwoBlowupRecursion.row i s) := by
  simp only [replay, ite_true, Finset.sum_const_zero, add_zero, constant_eq]

/-- A finite scalar certificate checks the original row once its collected columns are covered. -/
theorem replay_equation_iff {X : SurfaceTarget} (i : Fin X.blowups) (s : State X)
    (values : Variable X → ℚ) (states : List (State X))
    (hcover : ∀ v ∈ (RationalTerms.collect
      (SurfaceGenusTwoBlowupRecursion.row i s)).bind Prod.snd, v ∈ columns states) :
    replay i s values states = 0 ↔
      RationalTerms.eval values (SurfaceGenusTwoBlowupRecursion.row i s) = 0 := by
  rw [replay_eq_row i s values states hcover]

end AxiomaticGWTest.SurfaceGenusTwoBlowupScalar
