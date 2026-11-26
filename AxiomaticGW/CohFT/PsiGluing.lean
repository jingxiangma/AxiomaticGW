/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Tautological
public import Mathlib.Algebra.BigOperators.Option

/-!
# Cotangent monomials under elementary gluing

External ancestor powers restrict to their own component. The new node labels
have exponent zero: the input monomial has no cotangent class at a node.
These formulas follow from the existing individual cotangent pullback laws;
they introduce no extra geometric hypothesis or stable-map psi comparison.
-/

@[expose] public section

namespace AxiomaticGW.PsiClasses

open TensorProduct

universe u

/-- Restriction of external powers to the left component, with zero node power. -/
def separatingLeftPowers {S T : Type} (k : S ⊕ T → ℕ) : Option S → ℕ
  | none => 0
  | some s => k (.inl s)

/-- Restriction to the right component; its distinguished node also has power zero. -/
def separatingRightPowers {S T : Type} (k : S ⊕ T → ℕ) : Option T → ℕ
  | none => 0
  | some t => k (.inr t)

/-- Both distinguished self-gluing flags receive zero power. -/
def nonseparatingPowers {S : Type} (k : S → ℕ) : Option (Option S) → ℕ
  | none => 0
  | some none => 0
  | some (some s) => k s

/-- A primary left input remains primary after restricting to the component. -/
theorem separatingLeftPowers_zero {S T : Type} :
    separatingLeftPowers (0 : S ⊕ T → ℕ) = 0 := by
  funext s
  cases s <;> rfl

/-- The right restriction also preserves zero powers. -/
theorem separatingRightPowers_zero {S T : Type} :
    separatingRightPowers (0 : S ⊕ T → ℕ) = 0 := by
  funext t
  cases t <;> rfl

/-- Adding two zero node powers preserves a primary input. -/
theorem nonseparatingPowers_zero {S : Type} :
    nonseparatingPowers (0 : S → ℕ) = 0 := by
  funext s
  rcases s with _ | (_ | s) <;> rfl

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} (P : PsiClasses C)

/-- Pulling target powers back along the marking bijection recovers the target monomial. -/
theorem rename_monomial_comp (g : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (hS : StableArity g S) (hT : StableArity g T) (e : S ≃ T) (k : T → ℕ) :
    C.rename g S T hS hT e (P.monomial g S hS (k ∘ e)) =
      P.monomial g T hT k := by
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    P.rename_monomial g S T hS hT e (k ∘ e)

/-- The nonseparating pullback preserves all external powers and adds no node powers. -/
theorem nonseparating_monomial (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity (g + 1) S) (k : S → ℕ) :
    C.nonseparating g S h (P.monomial (g + 1) S h k) =
      P.monomial g (Option (Option S)) (StableArity.double_option_iff.mpr h)
        (nonseparatingPowers k) := by
  simp only [monomial, map_prod, map_pow, P.nonseparating_psi,
    Fintype.prod_option, nonseparatingPowers, pow_zero, one_mul]

/-- The separating pullback factors into monomials on the two components.
No multiplicativity of integration is needed or asserted. -/
theorem separating_monomial (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (k : S ⊕ T → ℕ) :
    C.separating g₁ g₂ S T h₁ h₂
      (P.monomial (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) k) =
      P.monomial g₁ (Option S) h₁ (separatingLeftPowers k) ⊗ₜ[R]
        P.monomial g₂ (Option T) h₂ (separatingRightPowers k) := by
  simp only [monomial, map_prod, Fintype.prod_sum_type, map_mul, map_pow,
    P.separating_psi_left, P.separating_psi_right, Algebra.TensorProduct.tmul_pow,
    one_pow, Fintype.prod_option, separatingLeftPowers, separatingRightPowers,
    pow_zero, one_mul]
  change (∏ s, (Algebra.TensorProduct.includeLeft : C.H g₁ (Option S) →ₐ[R]
      C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T))
      (P.psi g₁ (Option S) h₁ (some s) ^ k (.inl s))) *
    (∏ t, (Algebra.TensorProduct.includeRight : C.H g₂ (Option T) →ₐ[R]
      C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T))
      (P.psi g₂ (Option T) h₂ (some t) ^ k (.inr t))) = _
  rw [← map_prod, ← map_prod, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

end AxiomaticGW.PsiClasses
