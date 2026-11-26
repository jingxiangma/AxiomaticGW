/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EllipticHodge
public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgePicardMoments
public import AxiomaticGW.GKM.Fixtures.LoopSquareGluing
import all Mathlib.Data.List.Sort

/-! # Genus-two Hodge integrals on the normalizations of the Picard boundary

The elliptic Hodge class is represented by one twenty-fourth of the raw rational
self-gluing. On a separating normalization the two elliptic lines form a direct sum.
On a nonseparating normalization the quotient of the rank-two bundle by the elliptic
line is trivial. These class-level identifications are explicit geometric inputs.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoHodgeNormalization
open GenusTwoLocalizationClass LoopSeparatingGysin
open EllipticHodge (ellipticBoundary)
open HodgeDegreeOneRealization (loop separatingMarkedLeft)
open LoopSquareGluing (doubleLoopExpression)
open PointTarget.DVVCalculation GenusTwoHodgePicardMoments
open scoped TensorProduct

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- Restrictions of the two Chern classes to the actual normalizations of the two one-edge
divisors on the one-marked genus-two curve. The elliptic representatives have no free scalars. -/
structure Normalization (D : HodgeClasses C) (N : NonseparatingPushforward C I) : Prop where
  loop_first : C.nonseparating 1 (Fin 1) (stable 1) (D.first 1) =
    ellipticBoundary N loopStable
  loop_second : C.nonseparating 1 (Fin 1) (stable 1) (D.second 1) = 0
  separating_first : separatingPull C (D.first 1) =
    ellipticBoundary N markedStable ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] ellipticBoundary N unmarkedStable
  separating_second : separatingPull C (D.second 1) =
    ellipticBoundary N markedStable ⊗ₜ[ℚ] ellipticBoundary N unmarkedStable

/-- The two elliptic components each retain one rational normalization loop. -/
def bothRefinements : GluingExpression 2 (Fin 1) :=
  ((GluingExpression.fundamental 0 LeftNormalization leftStable).nonseparating.separating
    (GluingExpression.fundamental 0 RightNormalization rightStable).nonseparating).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)

/-- The normalizations and projection formulas express the four boundary products
as raw gluing classes with fixed coefficients. -/
theorem boundary_products (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (E : Normalization D N) :
    (D.first 1 : C.H 2 (Fin 1)) * loop.classValue F N =
        (1 / 24 : ℚ) • doubleLoopExpression.classValue F N ∧
    (D.second 1 : C.H 2 (Fin 1)) * loop.classValue F N = 0 ∧
    (D.first 1 : C.H 2 (Fin 1)) * separatingMarkedLeft.classValue F N =
        (1 / 24 : ℚ) • (leftRefinement.classValue F N + rightRefinement.classValue F N) ∧
    (D.second 1 : C.H 2 (Fin 1)) * separatingMarkedLeft.classValue F N =
        (1 / 576 : ℚ) • bothRefinements.classValue F N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change _ * N.push 1 (Fin 1) (stable 1) 1 =
      (1 / 24 : ℚ) • N.push 1 (Fin 1) (stable 1) (N.push 0 _ loopStable 1)
    rw [← N.projection_formula, E.loop_first, mul_one, ellipticBoundary, map_smul]
  · change _ * N.push 1 (Fin 1) (stable 1) 1 = 0
    rw [← N.projection_formula, E.loop_second, zero_mul, map_zero]
  · rw [HodgeLoopSeparatingProduct.separating_operator_value, separating_projection,
      E.separating_first, mul_one, ellipticBoundary, ellipticBoundary, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, ← smul_add, map_smul, map_add,
      HodgeLoopSeparatingProduct.leftRefinement_operator_value,
      HodgeLoopSeparatingProduct.rightRefinement_operator_value]
  · change _ * separatingPush F 1 = (1 / 576 : ℚ) •
      separatingPush F (N.push 0 _ markedStable 1 ⊗ₜ[ℚ] N.push 0 _ unmarkedStable 1)
    rw [separating_projection, E.separating_second, mul_one, ellipticBoundary, ellipticBoundary,
      TensorProduct.smul_tmul_smul, map_smul]
    norm_num

/-- After projection the two cotangent squares contribute one on the double loop and one
twenty-fourth on the ordered sum of single-loop refinements. The final three-edge graph has
cotangent integral one at the retained marking. -/
theorem component_rows :
    RationalTerms.collect (graphExpansion 4 doubleLoopExpression (fun _ ↦ 2)) =
      RationalTerms.term 1 0 ∧
    RationalTerms.collect (([leftRefinement, rightRefinement].map fun x ↦
      graphExpansion 4 x (fun _ ↦ 2)).sum) = RationalTerms.term (1 / 24) 0 ∧
    RationalTerms.collect (graphExpansion 4 bothRefinements (fun _ ↦ 1)) =
      RationalTerms.term 1 0 := by decide +kernel

private def psiIntegral (P : PsiClasses C) (I : StableCurveIntegration C) (k : ℕ) :
    C.H 2 (Fin 1) →ₗ[ℚ] ℚ :=
  (I.integrate 2 (Fin 1) (stable 1)).comp (LinearMap.mulLeft ℚ
    (P.monomial 2 (Fin 1) (stable 1) (fun _ ↦ k)))

private theorem component_integrals (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (dvv : PointTarget.DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24) :
    psiIntegral P I 2 (doubleLoopExpression.classValue F N) = 1 ∧
    psiIntegral P I 2 (leftRefinement.classValue F N + rightRefinement.classValue F N) =
      1 / 24 ∧ psiIntegral P I 1 (bothRefinements.classValue F N) = 1 := by
  have calcList (xs : List (GluingExpression 2 (Fin 1))) (k : ℕ) (v : ℚ)
      (hv : RationalTerms.collect ((xs.map fun x ↦ graphExpansion 4 x (fun _ ↦ k)).sum) =
        RationalTerms.term v 0) :
      psiIntegral P I k (xs.map (GluingExpression.classValue F N)).sum = v :=
    graphList_constant P F N dvv zero one 4 xs (stable 1) (fun _ ↦ k) v hv
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.map_singleton, List.sum_singleton] using
      calcList [doubleLoopExpression] 2 1 (by simpa only [List.map_singleton, List.sum_singleton]
        using component_rows.1)
  · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      calcList [leftRefinement, rightRefinement] 2 _ component_rows.2.1
  · simpa only [List.map_singleton, List.sum_singleton] using
      calcList [bothRefinements] 1 1 (by simpa only [List.map_singleton, List.sum_singleton]
        using component_rows.2.2)

/-- The top Hodge class against a marked cotangent square, via the square identity and the
normalization of the Picard row. -/
theorem second_square (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (E : Normalization D N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S} (B : PicardRealization D F N A)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (dvv : PointTarget.DVVRecursion P I) (zero : value P I 0 [0, 0, 0] = 1)
    (one : value P I 1 [1] = 1 / 24) : moment D P I 0 2 [2] = 7 / 5760 := by
  let L := psiIntegral P I 2
  have h := pairing B (L.comp (LinearMap.mulLeft ℚ (D.first 1 : C.H 2 (Fin 1))))
  obtain ⟨hl, _, hs, _⟩ := boundary_products F N E
  obtain ⟨vl, vs, _⟩ := component_integrals P F N dvv zero one
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
  rw [← pow_two, square, two_mul, map_add, hl, hs, map_smul, map_smul] at h
  change L (D.second 1) + L (D.second 1) =
    1 / 10 * (1 / 2 * (1 / 24 * _) + 2 * (1 / 24 * _)) at h
  change L _ = 1 at vl
  change L _ = 1 / 24 at vs
  rw [vl, vs] at h
  have hk : ([2] : List ℕ).get = (fun _ : Fin 1 ↦ 2) := by funext i; fin_cases i; rfl
  change I.integrate 2 (Fin 1) (stable 1)
    ((1 * (D.second 1 : C.H 2 (Fin 1))) * P.monomial 2 _ (stable 1) [2].get) = _
  rw [one_mul, hk, mul_comm]
  change L (D.second 1) = _
  linarith

/-- Pairing the top Chern class with the Picard row kills the nonseparating contribution. -/
theorem first_second_marked (P : PsiClasses C) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (E : Normalization D N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S} (B : PicardRealization D F N A)
    (dvv : PointTarget.DVVRecursion P I) (zero : value P I 0 [0, 0, 0] = 1)
    (one : value P I 1 [1] = 1 / 24) : moment D P I 1 2 [1] = 1 / 2880 := by
  let L := psiIntegral P I 1
  have h := pairing B (L.comp (LinearMap.mulLeft ℚ (D.second 1 : C.H 2 (Fin 1))))
  obtain ⟨_, hl, _, hs⟩ := boundary_products F N E
  obtain ⟨_, _, vs⟩ := component_integrals P F N dvv zero one
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
  rw [hl, map_zero, hs, map_smul] at h
  change L _ = 1 / 10 * (1 / 2 * 0 + 2 * (1 / 576 * _)) at h
  change L _ = 1 at vs
  rw [vs] at h
  have hk : ([1] : List ℕ).get = (fun _ : Fin 1 ↦ 1) := by funext i; fin_cases i; rfl
  change I.integrate 2 (Fin 1) (stable 1)
    (((D.first 1 : C.H 2 (Fin 1)) * D.second 1) * P.monomial 2 _ (stable 1) [1].get) = _
  rw [hk, mul_comm _ (P.monomial ..), mul_comm (D.first 1 : C.H 2 (Fin 1)) _]
  exact h.trans (by norm_num)

end AxiomaticGW.GKM.GenusTwoHodgeNormalization
