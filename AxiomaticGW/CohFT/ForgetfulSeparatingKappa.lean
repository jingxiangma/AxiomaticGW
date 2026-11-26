/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.GluingForgetful

/-!
# Kappa multiplication through separating gluing

The two new inputs below are proper pushforward composition along the two
placements of the forgotten marking. They apply to arbitrary source classes,
with explicit node/new-marking swaps and target label transports. They mention
neither kappa classes nor any product value. Their geometric satisfaction is
an independent obligation, not an axiom or a constructed moduli-space model.

The geometric mechanism is proper functoriality in Bae--Schmitt, `Chow rings
of stacks of prestable curves I`, Theorem 1.1 and Proposition 3.11:
https://arxiv.org/pdf/2012.09887 . Existing base change, psi pullback, and
projection formulas then derive the two component kappa contributions.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW

open TensorProduct

universe u

/-- Covariant functoriality for forgetting on either ordered component. Each
field is universal in both source classes, not a kappa-specific equality. -/
structure ForgetfulSeparatingComposition {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I) : Prop where
  push_left : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (z : C.H g₁ (Option (Option S))) (y : C.H g₂ (Option T)),
    Fforget.push (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
      (C.rename (g₁ + g₂) (Option S ⊕ T) (Option (S ⊕ T))
        (StableArity.separating h₁.option h₂) (StableArity.separating h₁ h₂).option
        (optionSumEquivLeft S T).symm
        (F.push g₁ g₂ (Option S) T h₁.option h₂
          (C.rename g₁ (Option (Option S)) (Option (Option S))
            h₁.option h₁.option (swapDoubleOption S) z ⊗ₜ[R] y))) =
      F.push g₁ g₂ S T h₁ h₂ (Fforget.push g₁ (Option S) h₁ z ⊗ₜ[R] y)
  push_right : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (x : C.H g₁ (Option S)) (z : C.H g₂ (Option (Option T))),
    Fforget.push (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
      (C.rename (g₁ + g₂) (S ⊕ Option T) (Option (S ⊕ T))
        (StableArity.separating h₁ h₂.option) (StableArity.separating h₁ h₂).option
        (optionSumEquivRight S T).symm
        (F.push g₁ g₂ S (Option T) h₁ h₂.option
          (x ⊗ₜ[R] C.rename g₂ (Option (Option T)) (Option (Option T))
            h₂.option h₂.option (swapDoubleOption T) z))) =
      F.push g₁ g₂ S T h₁ h₂ (x ⊗ₜ[R] Fforget.push g₂ (Option T) h₂ z)

namespace ForgetfulSeparatingComposition

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {Fforget : ForgetfulPushforward C I} {F : SeparatingPushforward C I}

/-- A target kappa factor contributes once on each component, for arbitrary
source insertions and every nonnegative kappa index. -/
theorem kappa_mul_push (Q : ForgetfulSeparatingComposition Fforget F)
    (P : PsiClasses C) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (m : ℕ) (x : C.H g₁ (Option S)) (y : C.H g₂ (Option T)) :
    P.kappa Fforget (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) m *
        F.push g₁ g₂ S T h₁ h₂ (x ⊗ₜ[R] y) =
      F.push g₁ g₂ S T h₁ h₂
        ((P.kappa Fforget g₁ (Option S) h₁ m * x) ⊗ₜ[R] y) +
      F.push g₁ g₂ S T h₁ h₂
        (x ⊗ₜ[R] (P.kappa Fforget g₂ (Option T) h₂ m * y)) := by
  let htarget := StableArity.separating h₁ h₂
  let ρL := C.rename (g₁ + g₂) (Option S ⊕ T) (Option (S ⊕ T))
    (StableArity.separating h₁.option h₂) htarget.option (optionSumEquivLeft S T).symm
  let ρR := C.rename (g₁ + g₂) (S ⊕ Option T) (Option (S ⊕ T))
    (StableArity.separating h₁ h₂.option) htarget.option (optionSumEquivRight S T).symm
  let σL := C.rename g₁ (Option (Option S)) (Option (Option S))
    h₁.option h₁.option (swapDoubleOption S)
  let σR := C.rename g₂ (Option (Option T)) (Option (Option T))
    h₂.option h₂.option (swapDoubleOption T)
  let p := P.psi (g₁ + g₂) (Option (S ⊕ T)) htarget.option none ^ (m + 1)
  let pL := P.psi (g₁ + g₂) (Option S ⊕ T)
    (StableArity.separating h₁.option h₂) (.inl none) ^ (m + 1)
  let pR := P.psi (g₁ + g₂) (S ⊕ Option T)
    (StableArity.separating h₁ h₂.option) (.inr none) ^ (m + 1)
  let qL := P.psi g₁ (Option (Option S)) h₁.option none ^ (m + 1)
  let qR := P.psi g₂ (Option (Option T)) h₂.option none ^ (m + 1)
  let fx := C.forget g₁ (Option S) h₁ x
  let fy := C.forget g₂ (Option T) h₂ y
  have hpL : ρL pL = p := by
    dsimp only [ρL, pL, p]
    rw [map_pow, P.rename_psi]
    rfl
  have hpR : ρR pR = p := by
    dsimp only [ρR, pR, p]
    rw [map_pow, P.rename_psi]
    rfl
  have hqL : C.separating g₁ g₂ (Option S) T h₁.option h₂ pL =
      σL qL ⊗ₜ[R] 1 := by
    dsimp only [pL, σL, qL]
    rw [map_pow, P.separating_psi_left, Algebra.TensorProduct.tmul_pow,
      one_pow, map_pow, P.rename_psi]
    rfl
  have hqR : C.separating g₁ g₂ S (Option T) h₁ h₂.option pR =
      1 ⊗ₜ[R] σR qR := by
    dsimp only [pR, σR, qR]
    rw [map_pow, P.separating_psi_right, Algebra.TensorProduct.tmul_pow,
      one_pow, map_pow, P.rename_psi]
    rfl
  have hκL : Fforget.push g₁ (Option S) h₁ (qL * fx) =
      P.kappa Fforget g₁ (Option S) h₁ m * x := by
    dsimp only [fx]
    rw [mul_comm qL, Fforget.projection_formula]
    exact mul_comm _ _
  have hκR : Fforget.push g₂ (Option T) h₂ (qR * fy) =
      P.kappa Fforget g₂ (Option T) h₂ m * y := by
    dsimp only [fy]
    rw [mul_comm qR, Fforget.projection_formula]
    exact mul_comm _ _
  have hleft : Fforget.push (g₁ + g₂) (S ⊕ T) htarget
        (ρL (F.push g₁ g₂ (Option S) T h₁.option h₂ (σL fx ⊗ₜ[R] y)) * p) =
      F.push g₁ g₂ S T h₁ h₂
        ((P.kappa Fforget g₁ (Option S) h₁ m * x) ⊗ₜ[R] y) := by
    calc
      _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
          (ρL (F.push g₁ g₂ (Option S) T h₁.option h₂
            (σL fx ⊗ₜ[R] y) * pL)) := by
        rw [← hpL, map_mul ρL]
      _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
          (ρL (F.push g₁ g₂ (Option S) T h₁.option h₂
            (C.separating g₁ g₂ (Option S) T h₁.option h₂ pL *
              (σL fx ⊗ₜ[R] y)))) := by
        rw [F.projection_formula]
        congr 2
        exact mul_comm _ _
      _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
          (ρL (F.push g₁ g₂ (Option S) T h₁.option h₂
            (σL (qL * fx) ⊗ₜ[R] y))) := by
        rw [hqL, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul σL]
      _ = F.push g₁ g₂ S T h₁ h₂
          (Fforget.push g₁ (Option S) h₁ (qL * fx) ⊗ₜ[R] y) :=
        Q.push_left g₁ g₂ S T h₁ h₂ (qL * fx) y
      _ = _ := by rw [hκL]
  have hright : Fforget.push (g₁ + g₂) (S ⊕ T) htarget
        (ρR (F.push g₁ g₂ S (Option T) h₁ h₂.option (x ⊗ₜ[R] σR fy)) * p) =
      F.push g₁ g₂ S T h₁ h₂
        (x ⊗ₜ[R] (P.kappa Fforget g₂ (Option T) h₂ m * y)) := by
    calc
      _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
          (ρR (F.push g₁ g₂ S (Option T) h₁ h₂.option
            (x ⊗ₜ[R] σR fy) * pR)) := by
        rw [← hpR, map_mul ρR]
      _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
          (ρR (F.push g₁ g₂ S (Option T) h₁ h₂.option
            (C.separating g₁ g₂ S (Option T) h₁ h₂.option pR *
              (x ⊗ₜ[R] σR fy)))) := by
        rw [F.projection_formula]
        congr 2
        exact mul_comm _ _
      _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
          (ρR (F.push g₁ g₂ S (Option T) h₁ h₂.option
            (x ⊗ₜ[R] σR (qR * fy)))) := by
        rw [hqR, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul σR]
      _ = F.push g₁ g₂ S T h₁ h₂
          (x ⊗ₜ[R] Fforget.push g₂ (Option T) h₂ (qR * fy)) :=
        Q.push_right g₁ g₂ S T h₁ h₂ x (qR * fy)
      _ = _ := by rw [hκR]
  calc
    _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
        (C.forget (g₁ + g₂) (S ⊕ T) htarget
          (F.push g₁ g₂ S T h₁ h₂ (x ⊗ₜ[R] y)) * p) := by
      rw [Fforget.projection_formula]
      exact mul_comm _ _
    _ = Fforget.push (g₁ + g₂) (S ⊕ T) htarget
        ((ρL (F.push g₁ g₂ (Option S) T h₁.option h₂ (σL fx ⊗ₜ[R] y)) +
          ρR (F.push g₁ g₂ S (Option T) h₁ h₂.option (x ⊗ₜ[R] σR fy))) * p) := by
      rw [H.separating]
    _ = _ := by rw [add_mul, map_add, hleft, hright]

end ForgetfulSeparatingComposition

end AxiomaticGW
