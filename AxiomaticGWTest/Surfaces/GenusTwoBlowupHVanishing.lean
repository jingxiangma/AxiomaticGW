/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHVanishing

/-!
# Shifted-H constructor-vanishing consumer regressions

These tests distinguish the seven external-state chains from the three rational
H/Ei forks, cover the class-zero boundary of each argument, retain arbitrary
remainders, and instantiate negative signed multiplicities and both Bl2P2
exceptional generators. They use the proved uniform identities, rather than
numerical evaluation of the original graph coefficients.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHVanishing
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo SurfaceGenusTwoBlowupHPivots
  SurfaceGenusTwoBlowupHVanishing

/-- The resulting identity concerns the complete original normalized row. -/
theorem original_row_two_contributions (X : SurfaceTarget) (i : Fin X.blowups)
    (beta : X.Curve) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (row X i beta) {hColumn X beta} =
      survivingCoefficient X i beta (X.exceptionalCurve i) :=
  row_coefficient_eq_surviving_of_pos X i beta hbeta

/-- Wrong-descendant-state vanishing has no point-budget or class restriction. -/
theorem exceptional_descendant_arbitrary_budget (X : SurfaceTarget)
    (beta delta : X.Curve) (i : Fin X.blowups) (n : ℕ) :
    remainderVertex X (hColumn X beta) (coefficientVertex X (hColumn X beta)) n
      2 (Fin 2) (by norm_num [StableArity]) (Pi.single 0 1) inferInstance delta
      ![.exceptional i, .point] = 0 := by
  apply remainderVertex_wrong_label_eq_zero X beta delta n (Fin 2) _ 0 _
  intro he
  cases he

/-- A fork also vanishes at a zero-energy request and arbitrary point count;
this uses its rational H/Ei component, not a positive-energy genus-two theorem. -/
theorem fork_class_zero_arbitrary_budget (n : ℕ) :
    remainderPointCoefficient .hirzebruchOne (hColumn .hirzebruchOne 0)
      (coefficientVertex .hirzebruchOne (hColumn .hirzebruchOne 0))
      (L24Gluing.term (52 : Fin 815)) 0 n (labels .hirzebruchOne 0) = 0 :=
  rationalHyperplaneExceptionalFrame_coefficient_zero .hirzebruchOne 0 0
    (by decide +kernel) n 0 52 (by decide +kernel)

/-- The classical zero-class H/Ei cup product vanishes even with added points. -/
theorem classical_hyperplane_exceptional_zero (X : SurfaceTarget)
    (i : Fin X.blowups) (n : ℕ) (b : SurfaceBasisLabel X) (f : X.Curve → ℚ) :
    SurfaceGenusZero.primaryScalar X f 0 n ![.hyperplane, .exceptional i, b] = 0 :=
  primaryScalar_hyperplane_exceptional_eq_zero X i f 0 (map_zero _) n b

/-- F1 coordinates (2,1) have negative signed exceptional multiplicity. No
irreducibility or nonnegative-multiplicity restriction is introduced. -/
theorem negative_signed_multiplicity_ten_terms :
    SurfaceTarget.hirzebruchOne.signedMultiplicity ![2, 1] 0 = -1 ∧
    ∀ j ∈ vanishingFrame,
      remainderPointCoefficient .hirzebruchOne (hColumn .hirzebruchOne ![2, 1])
        (firstCoefficientVertex .hirzebruchOne ![2, 1] .hyperplane
          (SurfaceTarget.hirzebruchOne.effective.energy ![2, 1]))
        (L24Gluing.term j) (SurfaceTarget.hirzebruchOne.exceptionalCurve 0)
        (pointCount .hirzebruchOne ![2, 1]) (labels .hirzebruchOne 0) = 0 := by
  refine ⟨by decide +kernel, ?_⟩
  exact shifted_vanishingFrame_coefficient_zero .hirzebruchOne 0 ![2, 1]
    (by decide +kernel)

/-- Both exceptional generators are accepted on a mixed Bl2P2 class. -/
theorem mixed_blowup_two_both_exceptional (i : Fin 2) :
    ∀ j ∈ vanishingFrame,
      remainderPointCoefficient .blowupTwo (hColumn .blowupTwo ![2, 3, 1])
        (firstCoefficientVertex .blowupTwo ![2, 3, 1] .hyperplane
          (SurfaceTarget.blowupTwo.effective.energy ![2, 3, 1]))
        (L24Gluing.term j) (SurfaceTarget.blowupTwo.exceptionalCurve i)
        (pointCount .blowupTwo ![2, 3, 1]) (labels .blowupTwo i) = 0 :=
  shifted_vanishingFrame_coefficient_zero .blowupTwo i ![2, 3, 1] (by decide +kernel)

/-- The seven chains retain every full effective remainder; only the main budget
is bounded by the requested energy. -/
theorem chains_keep_arbitrary_remainder (X : SurfaceTarget) (i : Fin X.blowups)
    (beta delta : X.Curve) (n : ℕ) (hn : n < X.effective.energy beta) :
    ∀ j ∈ externalExceptionalFrame,
    remainderPointCoefficient X (hColumn X beta) (coefficientVertex X (hColumn X beta))
      (L24Gluing.term j) delta n (labels X i) = 0 :=
  externalExceptionalFrame_coefficient_zero X beta delta n hn i

/-- Natural subtraction at class zero cannot authorize the positive-energy pruning. -/
theorem class_zero_excluded (X : SurfaceTarget) :
    ¬0 < X.effective.energy (0 : X.Curve) := by
  rw [map_zero]
  exact Nat.not_lt_zero _

/-- A different exceptional remainder is preserved in the original source
coefficient. Equality of energies does not identify the two full class columns. -/
theorem other_exceptional_remainder (i j : Fin 2) (beta : SurfaceTarget.blowupTwo.Curve)
    (hbeta : 0 < SurfaceTarget.blowupTwo.effective.energy beta) :
    L24Relation.pointCoefficient .blowupTwo (pointCount .blowupTwo beta)
      (beta + SurfaceTarget.blowupTwo.exceptionalCurve j)
      (labels .blowupTwo i) (hColumn .blowupTwo beta) =
      survivingCoefficient .blowupTwo i beta (SurfaceTarget.blowupTwo.exceptionalCurve j) :=
  pointCoefficient_eq_surviving_of_planeDegree_zero .blowupTwo i beta
    (SurfaceTarget.blowupTwo.exceptionalCurve j) hbeta
    (SurfaceTarget.blowupTwo.planeDegree_exceptionalCurve j)

end AxiomaticGWTest.SurfaceGenusTwoBlowupHVanishing
