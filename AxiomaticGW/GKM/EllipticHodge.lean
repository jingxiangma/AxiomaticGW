/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.PointTarget.GenusZeroMultinomial
public import AxiomaticGW.CohFT.GluingForgetful
public import AxiomaticGW.CohFT.PsiGluing

/-! # The elliptic Hodge factor appearing in the GKM vertex formula

The elliptic Hodge line is represented by one twenty-fourth of the raw
nonseparating pushforward. Its square vanishes in all arities and its top cotangent
integrals are genus-zero multinomials divided by 24. Application to a Hodge bundle
requires its first Chern class to agree with this boundary representative.
-/

@[expose] public section
namespace AxiomaticGW.GKM.EllipticHodge
open PsiBoundaryExpansion

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}

/-- The elliptic Hodge representative in the labeled raw Gysin convention. -/
def ellipticBoundary (N : NonseparatingPushforward C I) {S : Type} [Fintype S]
    (h : StableArity 1 S) : C.H 1 S := (1 / 24 : ℚ) • N.push 0 S h 1

/-- Forgetting a marking pulls back the whole representative with its normalization. -/
theorem forget (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (G : GluingForgetfulCompatibility F N) {S : Type} [Fintype S] (h : StableArity 1 S) :
    C.forget 1 S h (ellipticBoundary N h) = ellipticBoundary N h.option := by
  rw [ellipticBoundary, map_smul, G.nonseparating, map_one, map_one, ellipticBoundary]

/-- The representative respects changes of the original external labels. -/
theorem rename (N : NonseparatingPushforward C I) {S T : Type} [Fintype S] [Fintype T]
    (h : StableArity 1 S) (h' : StableArity 1 T) (e : S ≃ T) :
    C.rename 1 S T h h' e (ellipticBoundary N h) = ellipticBoundary N h' := by
  have eq := congrArg (fun f ↦ f (1 : C.H 0 (Option (Option S)))) (N.push_rename 0 S T h h' e)
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one] at eq
  rw [ellipticBoundary, map_smul, ← eq, ellipticBoundary]

private theorem stable (n : ℕ) : StableArity 1 (Fin (n + 1)) := by
  simp only [StableArity, Fintype.card_fin]
  omega

/-- On the one-marked curve the square has excess degree. Naturality transports this
class identity to every nonempty finite marking set. -/
theorem square_zero (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (G : GluingForgetfulCompatibility F N) {S : Type} [Fintype S] (h : StableArity 1 S) :
    ellipticBoundary N h ^ 2 = 0 := by
  have ordered (n : ℕ) : ellipticBoundary N (stable n) ^ 2 = 0 := by
    induction n with
    | zero =>
      apply C.eq_zero_of_dimension_lt 1 _ (stable 0) 2
      · have hx : ellipticBoundary N (stable 0) ∈ (C.H 1 (Fin 1)).degree 1 :=
          ((C.H 1 _).degree 1).smul_mem _ (N.push_degree 0 _ (stable 0) 0 1
            SetLike.GradedOne.one_mem)
        simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded 2 hx
      · decide
    | succ n ih =>
      apply (C.rename 1 _ _ (stable (n + 1)) (stable n).option (finSuccEquiv (n + 1))).injective
      rw [map_pow, rename N, map_zero, ← forget F N G (stable n), ← map_pow, ih, map_zero]
  have hn : 0 < Fintype.card S := by
    unfold StableArity at h
    omega
  let n := Fintype.card S - 1
  let e : Fin (n + 1) ≃ S := Fintype.equivOfCardEq (by rw [Fintype.card_fin]; dsimp [n]; omega)
  rw [← rename N (stable n) h e, ← map_pow, ordered, map_zero]

/-- The native one-lambda branch for arbitrary powers follows from the raw curve gluing.
It includes the off-dimension zero and the case of just one elliptic marking. -/
theorem integral (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    {S : Type} [Fintype S] (h : StableArity 1 S) (d : S → ℕ) :
    I.integrate 1 S h (P.monomial 1 S h d * ellipticBoundary N h) =
      if (∑ s, d s) + 1 = Fintype.card S then
        ((Fintype.card S - 1).factorial : ℚ) / (24 * ∏ s, ((d s).factorial : ℚ)) else 0 := by
  have hs := StableArity.double_option_iff.mpr h
  have val := PointTarget.genusZero_intersection_of_geometry U F N P K hK T vol hs
    (PsiClasses.nonseparatingPowers d)
  rw [PointTarget.intersectionNumber_of_stable P I _ _ hs] at val
  rw [ellipticBoundary, mul_smul_comm, map_smul, N.integrate_mul_push,
    P.nonseparating_monomial, mul_one, val]
  simp only [Fintype.sum_option, Fintype.prod_option, PsiClasses.nonseparatingPowers,
    Fintype.card_option, zero_add, Nat.factorial_zero, Nat.cast_one, one_mul, smul_eq_mul]
  have hn : 0 < Fintype.card S := by unfold StableArity at h; omega
  have he : Fintype.card S + 1 + 1 - 3 = Fintype.card S - 1 := by omega
  rw [he]
  by_cases ht : (∑ s, d s) + 1 = Fintype.card S
  · rw [if_pos ht, if_pos (by omega : (∑ s, d s) = Fintype.card S - 1)]
    ring
  · rw [if_neg ht, if_neg (by omega : (∑ s, d s) ≠ Fintype.card S - 1), mul_zero]

end AxiomaticGW.GKM.EllipticHodge
