/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHOtherFamilies

/-!
# Consumers of the complete shifted H support

Arbitrary full remainders, class zero and energy-one seeds test the rational
mechanism. Same-plane columns on F1 and Bl2P2 retain signed multiplicities,
foreign exceptional coordinates and arbitrary requested point counts.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHOtherFamilies
open AxiomaticGW SurfaceGenusTwoBlowupHPivots SurfaceGenusTwoBlowupHOtherFamilies

/-- The full normalized coefficient vanishes for every primary request and pure remainder. -/
theorem arbitrary_primary_full_remainder (X : SurfaceTarget) (i : Fin X.blowups)
    (gamma delta : X.Curve) (hd : X.planeDegree delta = 0) (n k : ℕ) :
    L24Relation.pointCoefficient X n (gamma + delta) (labels X i)
      (.inr (SurfaceQuery.points X 2 gamma k)) = 0 :=
  pointCoefficient_primary_eq_zero_of_planeDegree_zero X gamma delta hd n k i

/-- An arbitrary exceptional request is excluded without a nonnegative multiplicity premise. -/
theorem arbitrary_exceptional_full_remainder (X : SurfaceTarget) (i j : Fin X.blowups)
    (gamma delta : X.Curve) (hd : X.planeDegree delta = 0) (count n : ℕ) :
    L24Relation.pointCoefficient X n (gamma + delta) (labels X i)
      (.inr (SurfaceFirstDescendant.query 2 gamma (.exceptional j) count)) = 0 :=
  pointCoefficient_first_other_eq_zero_of_planeDegree_zero X gamma delta hd
    (.exceptional j) count n (by intro h; cases h) i

/-- Arbitrary added points and requested counts remain valid at class zero. -/
theorem class_zero_primary (X : SurfaceTarget) (i : Fin X.blowups) (n k : ℕ) :
    L24Relation.pointCoefficient X n 0 (labels X i)
      (.inr (SurfaceQuery.points X 2 0 k)) = 0 := by
  simpa only [add_zero] using
    pointCoefficient_primary_eq_zero_of_planeDegree_zero X 0 0 (map_zero _) n k i

/-- The rational exceptional-point scalar vanishes despite the preserved energy-one seed. -/
theorem energy_one_seed_and_point_scalar (X : SurfaceTarget) (i : Fin X.blowups)
    (node : SurfaceBasisLabel X) (n : ℕ) :
    SurfaceGenusZero.pointValue X (X.exceptionalCurve i) = 1 ∧
      SurfaceGenusZero.primaryScalar X (SurfaceGenusZero.pointValue X)
        (X.exceptionalCurve i) n ![.exceptional i, .point, node] = 0 :=
  ⟨SurfaceGenusZero.pointValue_exceptional_generator X i,
    primaryScalar_exceptional_point_zero X i _ (X.planeDegree_exceptionalCurve i) n node⟩

/-- Mixed reducible pure exceptional classes keep both exceptional coordinates. -/
theorem mixed_exceptional_point_scalar (n : ℕ) (node : SurfaceBasisLabel .blowupTwo) :
    SurfaceGenusZero.primaryScalar .blowupTwo (SurfaceGenusZero.pointValue .blowupTwo)
      ![2, 3, 0] n ![.exceptional 0, .point, node] = 0 :=
  primaryScalar_exceptional_point_zero .blowupTwo 0 _ rfl n node

/-- F1 at negative signed multiplicity has no primary dependency at the same plane degree. -/
theorem hirzebruchOne_negative_multiplicity_primary (k : ℕ) :
    RationalTerms.coefficient (row .hirzebruchOne 0 ![2, 1])
      {.inr (SurfaceQuery.points .hirzebruchOne 2 ![5, 1] k)} = 0 :=
  primary_row_coefficient_eq_zero_of_same_planeDegree .hirzebruchOne 0 _ _ k rfl

/-- A different Bl2P2 full class and requested point count cannot produce a P coupling. -/
theorem blowupTwo_foreign_full_class_point (count : ℕ) :
    RationalTerms.coefficient (row .blowupTwo 0 ![2, 3, 1])
      {.inr (SurfaceFirstDescendant.query 2 ![3, 2, 1] .point count)} = 0 :=
  first_other_row_coefficient_eq_zero_of_same_planeDegree .blowupTwo 0 _ _ .point
    count (by intro h; cases h) rfl

/-- The E1-shifted row excludes the E2 descendant at positive plane degree. -/
theorem blowupTwo_foreign_exceptional_column (count : ℕ) :
    RationalTerms.coefficient (row .blowupTwo 0 ![0, 1, 1])
      {.inr (SurfaceFirstDescendant.query 2 ![1, 0, 1] (.exceptional 1) count)} = 0 :=
  first_other_row_coefficient_eq_zero_of_same_planeDegree .blowupTwo 0 _ _ (.exceptional 1)
    count (by intro h; cases h) rfl

/-- The original row's bound also excludes a same-plane class outside its effective source. -/
theorem outside_source_primary (k : ℕ) :
    RationalTerms.coefficient (row .blowupTwo 1 ![1, 0, 1])
      {.inr (SurfaceQuery.points .blowupTwo 2 ![4, 5, 1] k)} = 0 :=
  primary_row_coefficient_eq_zero_of_same_planeDegree .blowupTwo 1 _ _ k rfl

/-- Public support applies to the actual row, with no supplied effective split or support oracle. -/
theorem original_row_canonical_support (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve) (family : SurfaceGenusTwoBlowupOrder.Family X)
    (hp : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient (row X i beta) {.inr (family.query gamma)} ≠ 0) :
    (family = .hyperplane ∧ gamma = beta) ∨
      SurfaceGenusTwoBlowupOrder.Earlier X (gamma, family) (beta, .hyperplane) :=
  canonical_coefficient_support X i beta gamma family hp hc

end AxiomaticGWTest.SurfaceGenusTwoBlowupHOtherFamilies
