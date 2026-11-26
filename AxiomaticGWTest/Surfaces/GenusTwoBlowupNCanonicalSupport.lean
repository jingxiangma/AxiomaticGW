/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupNCanonicalSupport

/-! Consequences for exact N dependencies and retained boundary coefficients. -/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupNCanonicalSupport
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupNCanonicalSupport SurfaceGenusTwoBlowupNCoefficients

/-- At equal plane degree a different primary full class must strictly lower energy. -/
theorem primary_strict_energy (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve) (hd : X.planeDegree gamma = X.planeDegree beta)
    (hne : gamma ≠ beta)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (Family.primary.query gamma)} ≠ 0) :
    X.effective.energy gamma < X.effective.energy beta := by
  rcases primary_coefficient_support i beta gamma hc with hg | he
  · exact (hne hg).elim
  · rw [earlier_iff] at he
    rcases he with he | ⟨_, he | ⟨_, he⟩⟩
    · exact (Nat.lt_irrefl _ (hd ▸ he)).elim
    · exact (Nat.lt_irrefl _ he).elim
    · exact he

/-- The N solver may use the earlier H family without an energy-decrease premise. -/
theorem hyperplane_earlier (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {Sum.inr (Family.hyperplane.query gamma)} ≠ 0) :
    Earlier X (gamma, .hyperplane) (beta, .primary) := by
  rcases canonical_coefficient_support i beta gamma .hyperplane hc with ⟨_, he⟩ | he
  · cases he
  · exact he

/-- A nonzero degree-two primary pivot remains while its competing diagonal K vanishes. -/
theorem degree_two_pivot_and_exceptional :
    let beta : SurfaceTarget.blowupTwo.Curve := ![0,0,2]
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0 beta)
      {Sum.inr ((Family.exceptional 0).query beta)} = 0 ∧
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0 beta)
      {Sum.inr (Family.primary.query beta)} = 12 := by
  dsimp only
  constructor
  · exact row_exceptional_coefficient_eq_zero_of_same_planeDegree 0 0 _ _ rfl
  · exact (row_primary_coefficient (X := .blowupTwo) 0 ![0,0,2]).trans (by
      change 6 * (2 : ℚ) = 12
      norm_num)

/-- Mixed reducible exceptional remainders retain both full coordinates and all K labels. -/
theorem mixed_remainder_exceptional_zero :
    let beta : SurfaceTarget.blowupTwo.Curve := ![1,3,2]
    let gamma : SurfaceTarget.blowupTwo.Curve := ![0,0,2]
    let delta : SurfaceTarget.blowupTwo.Curve := ![2,3,0]
    gamma + delta = beta + SurfaceTarget.blowupTwo.exceptionalCurve 0 ∧
    ∀ j : Fin 2, RationalTerms.coefficient
      (SurfaceGenusTwoBlowupNRelation.row .blowupTwo 0 beta)
      {Sum.inr ((Family.exceptional (X := .blowupTwo) j).query gamma)} = 0 := by
  dsimp only
  constructor
  · decide +kernel
  · intro j
    exact row_exceptional_coefficient_eq_zero_of_same_planeDegree (X := .blowupTwo)
      0 j _ _ rfl

/-- Class-zero exceptional columns vanish without a positive-energy or pivot premise. -/
theorem class_zero_exceptional (X : SurfaceTarget) (i j : Fin X.blowups) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i 0)
      {Sum.inr ((Family.exceptional j).query 0)} = 0 := by
  exact row_exceptional_coefficient_eq_zero_of_same_planeDegree i j 0 0 rfl

end AxiomaticGWTest.SurfaceGenusTwoBlowupNCanonicalSupport
