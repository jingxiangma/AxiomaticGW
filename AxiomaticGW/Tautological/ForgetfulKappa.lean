/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.RationalTailPullback

/-!
# Kappa pullback and products from the universal-curve square

Two additional universal map laws are explicit geometric inputs: proper/flat
base change through the two-marking resolution of the universal-curve fibre
product, and proper composition after contracting the actual rational-tail
section. Neither input mentions kappa, its powers, or a desired product.

The existing psi-power correction then derives kappa pullback and a formula
for forgetting one kappa insertion times the new psi power. See Bae--Schmitt,
`Chow rings of stacks of prestable curves I`, Proposition 3.10, diagram (22),
and Proposition 3.11: https://arxiv.org/pdf/2012.09887 . The diagram is a
resolution of the fibre product; no claim that it is Cartesian is made here.

This constructs conditional cohomology identities. It does not provide a
covariant forgetful operation on the free strata module or identify an
arbitrary linear realization of a kappa-squared raw corolla.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW

universe u

/-- Universal map compatibility for the resolved forgetful square and its
contracted two-marking rational-tail section. Satisfaction remains geometric. -/
structure ForgetfulSquareCompatibility {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I) : Prop where
  /-- Pull a proper pushforward back through the resolved universal-curve square. -/
  base_change : ∀ (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
      (z : C.H g (Option S)),
    C.forget g S h (Fforget.push g S h z) =
      Fforget.push g (Option S) h.option
        (C.rename g (Option (Option S)) (Option (Option S)) h.option.option
          h.option.option (swapDoubleOption S)
          (C.forget g (Option S) h.option z))
  /-- Contracting the actual tail after swapping its two markings is the
  identity on its arbitrary main-component insertion. -/
  contract_tail : ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (h : StableArity g S) (z : C.H g (Option S)),
    Fforget.push g (Option S) h.option
      (C.rename g (Option (Option S)) (Option (Option S)) h.option.option
        h.option.option (swapDoubleOption S)
        (PsiBoundaryExpansion.tailPush F h.option none z)) = z

namespace ForgetfulSquareCompatibility

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {Fforget : ForgetfulPushforward C I} {F : SeparatingPushforward C I}

/-- The new-marking correction to kappa pullback is derived from the existing
psi-power correction and universal map laws, including the index-zero case. -/
theorem forget_kappa (Q : ForgetfulSquareCompatibility Fforget F)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (m : ℕ) :
    C.forget g S h (P.kappa Fforget g S h m) =
      P.kappa Fforget g (Option S) h.option m -
        P.psi g (Option S) h.option none ^ m := by
  classical
  let σ := C.rename g (Option (Option S)) (Option (Option S))
    h.option.option h.option.option (swapDoubleOption S)
  have hp := PsiBoundaryExpansion.forget_psi_pow_succ F N P K hK H
    h.option (none : Option S) m
  have hswap : σ (P.psi g (Option (Option S)) h.option.option (some none) ^ (m + 1)) =
      P.psi g (Option (Option S)) h.option.option none ^ (m + 1) := by
    dsimp only [σ]
    rw [map_pow, P.rename_psi]
    rfl
  calc
    _ = Fforget.push g (Option S) h.option
        (σ (C.forget g (Option S) h.option
          (P.psi g (Option S) h.option none ^ (m + 1)))) :=
      Q.base_change g S h _
    _ = Fforget.push g (Option S) h.option
        (σ (P.psi g (Option (Option S)) h.option.option (some none) ^ (m + 1) -
          PsiBoundaryExpansion.tailPush F h.option none
            (P.psi g (Option S) h.option none ^ m))) := by rw [hp]
    _ = _ := by
      rw [map_sub σ, map_sub, hswap,
        Q.contract_tail g S h (P.psi g (Option S) h.option none ^ m)]
      rfl

/-- Forgetting one kappa insertion with a new-marking psi power produces the
two-index product and the merged kappa index, with coefficient one each. -/
theorem push_kappa_mul_newPsi (Q : ForgetfulSquareCompatibility Fforget F)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (a b : ℕ) :
    Fforget.push g S h
        (P.kappa Fforget g (Option S) h.option a *
          P.psi g (Option S) h.option none ^ (b + 1)) =
      P.kappa Fforget g S h a * P.kappa Fforget g S h b +
        P.kappa Fforget g S h (a + b) := by
  have hk : P.kappa Fforget g (Option S) h.option a =
      C.forget g S h (P.kappa Fforget g S h a) +
        P.psi g (Option S) h.option none ^ a :=
    (sub_eq_iff_eq_add).mp (Q.forget_kappa N P K hK H g S h a).symm
  rw [hk, add_mul, map_add, Fforget.projection_formula]
  change P.kappa Fforget g S h a * P.kappa Fforget g S h b +
      Fforget.push g S h
        (P.psi g (Option S) h.option none ^ a *
          P.psi g (Option S) h.option none ^ (b + 1)) =
    P.kappa Fforget g S h a * P.kappa Fforget g S h b +
      Fforget.push g S h (P.psi g (Option S) h.option none ^ (a + b + 1))
  rw [← pow_add, Nat.add_assoc]

/-- The degree-two kappa product is the corrected forgetful pushforward.
This is a cohomology identity, not a statement about a free-strata realization. -/
theorem kappa_one_square (Q : ForgetfulSquareCompatibility Fforget F)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) :
    P.kappa Fforget g S h 1 ^ 2 =
      Fforget.push g S h
        (P.kappa Fforget g (Option S) h.option 1 *
          P.psi g (Option S) h.option none ^ 2) - P.kappa Fforget g S h 2 := by
  have hp := Q.push_kappa_mul_newPsi N P K hK H g S h 1 1
  rw [← pow_two] at hp
  exact (eq_sub_iff_add_eq).mpr hp.symm

end ForgetfulSquareCompatibility

end AxiomaticGW
