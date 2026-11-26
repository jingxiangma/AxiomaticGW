/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeNormalization
public import AxiomaticGW.GKM.Fixtures.HodgeBoundarySquareCertificate

/-! # Recovering the rank-two square from the actual Hodge packets

On the one-marked genus-two curve, the original PPZ relations express 960 λ₂
as the labeled double loop plus four copies of each of the two mixed refinements.
Multiplying the Picard relation by λ₁ gives the same refinement classes through
the Hodge restrictions to the two boundary normalizations.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoHodgeNormalizedPacket
open HodgeBoundarySquareRows (columns rows half)
open GenusTwoLocalizationClass GenusTwoHodgePicardMoments GenusTwoHodgeNormalization
open AdmcyclesHodgeStrataCandidates RelationCertificate
open LoopSquareGluing (doubleLoopExpression)
open LoopSeparatingGysin (leftRefinement rightRefinement)

/-- These are raw pushforwards. The two separating refinements keep the marked and
unmarked components distinct. -/
def refinements : Coordinates 17 :=
  Pi.single 16 1 + (4 : ℚ) • (Pi.single 15 1 + Pi.single 14 1)

/-- Multipliers obtained from the full-stable original fourteen-generator presentation. -/
def witness : Certificate 14 := ⟨
  ![4/27, -1/2592, 5/7776, -2/3, 1/972, -1/324, -4/27, 10/27, 0, 20/27, -20/27, 2/27, 0, 0]⟩

/-- The requested residual is checked in every raw graph coordinate. -/
theorem checked : check rows ((960 : ℚ) • half - refinements) witness = true := by decide +kernel

private theorem interpret_single (i : Fin 17) :
    interpret columns (Pi.single i 1) = StrataModule.basis (columns i) := by
  simp only [interpret_apply, Pi.single_apply, ite_smul, zero_smul, one_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- The second Chern class is identified with the actual sixteen-term admcycles packet.
The three graph realizations and the original relations have a class-level meaning. -/
structure SecondRealization (D : HodgeClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) : Prop where
  second : (D.second 1 : C.H 2 (Fin 1)) = (A 2 (Fin 1)).map raw02Degree2
  relation : ∀ i, witness.weights i ≠ 0 →
    (A 2 (Fin 1)).map (interpret columns (rows i)) = 0
  double : doubleLoopExpression.Compatible A F N
  marked : leftRefinement.Compatible A F N
  unmarked : rightRefinement.Compatible A F N

/-- The original second Chern packet becomes an explicit sum of three normalized strata. -/
theorem second_eq {F : SeparatingPushforward C I} {N : NonseparatingPushforward C I}
    {A : ∀ g S, [Fintype S] → StrataRealization C g S} (S : SecondRealization D F N A) :
    (D.second 1 : C.H 2 (Fin 1)) = (1 / 960 : ℚ) • (doubleLoopExpression.classValue F N +
      (4 : ℚ) • (leftRefinement.classValue F N + rightRefinement.classValue F N)) := by
  let ev := (A 2 (Fin 1)).map
  have h : ev (interpret columns ((960 : ℚ) • half - refinements)) = 0 := by
    rw [← (check_eq_true_iff _ _ _).mp checked, interpret_combination, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    by_cases hi : witness.weights i ≠ 0
    · rw [show ev _ = 0 from S.relation i hi, smul_zero]
    · rw [not_ne_iff.mp hi, zero_smul]
  rw [map_sub, map_smul, HodgeBoundarySquareCertificate.interpret_half, map_sub, map_smul,
    sub_eq_zero] at h
  have frame : ev (interpret columns refinements) =
      doubleLoopExpression.classValue F N +
      (4 : ℚ) • (leftRefinement.classValue F N + rightRefinement.classValue F N) := by
    simp only [refinements, map_add, map_smul, interpret_single]
    change ev (StrataModule.basis rawGraph12) +
      (4 : ℚ) • (ev (StrataModule.basis rawGraph18) + ev (StrataModule.basis rawGraph19)) = _
    rw [LoopSquareGluing.rawGraph12_eq_doubleLoop,
      HodgeLoopSeparatingProduct.rawGraph18_eq_leftRefinement,
      HodgeLoopSeparatingProduct.rawGraph19_eq_rightRefinement]
    dsimp only [ev]
    rw [doubleLoopExpression.map_stratum_eq_classValue A F N S.double,
      leftRefinement.map_stratum_eq_classValue A F N S.marked,
      rightRefinement.map_stratum_eq_classValue A F N S.unmarked]
  rw [S.second, ← frame, ← h, smul_smul]
  norm_num [ev]

/-- The one-marked rank-two square follows from the two actual packet identifications,
the original PPZ rows and restriction of λ₁ to the two boundary normalizations. -/
theorem square {F : SeparatingPushforward C I} {N : NonseparatingPushforward C I}
    {A : ∀ g S, [Fintype S] → StrataRealization C g S} (B : PicardRealization D F N A)
    (E : Normalization D N) (S : SecondRealization D F N A) :
    (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)) := by
  have first := B.first.trans (HodgeGenusTwoPicard.map_degree_one _ B.row)
  rw [HodgeGenusTwoPicard.map_boundary A F N B.loopMap B.separatingMap] at first
  obtain ⟨loop, _, sep, _⟩ := boundary_products F N E
  rw [pow_two]
  nth_rw 2 [first]
  rw [mul_smul_comm, mul_add, mul_smul_comm, mul_smul_comm, loop, sep, two_mul, second_eq S]
  simp only [smul_add, smul_smul]
  module

end AxiomaticGW.GKM.GenusTwoHodgeNormalizedPacket
