/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.SeparatingPushforward
public import AxiomaticGW.CohFT.NonseparatingPushforward

/-!
# Forgetful pullback of elementary gluing pushforwards

These two primitive cohomology laws express base change for the universal
curve and a gluing map. In the separating case the new marking lies on either
component, so the two raw pushforwards add. In the nonseparating case there is
one source component, with its two node labels preserved by an explicit
permutation. No automorphism divisor occurs in either raw formula.

The geometric source is Bae--Schmitt, *Chow rings of stacks of prestable curves I*,
Proposition 3.8 and Corollary 3.9. This interface records geometric input; it
does not construct the moduli spaces. It contains no graph relation, GW class
family, or numerical recurrence. It is separate from the existing commuting
pullback laws, which do not by themselves imply pushforward base change.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Primitive universal-curve base change for the two raw gluing maps. -/
structure GluingForgetfulCompatibility {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) : Prop where
  /-- The added marking survives while both old node labels are glued. -/
  nonseparating : ∀ (g : ℕ) (S : Type) [Fintype S]
      (h : StableArity (g + 1) S) (x : C.H g (Option (Option S))),
    C.forget (g + 1) S h (N.push g S h x) =
      N.push g (Option S) h.option
        (C.rename g (Option (Option (Option S))) (Option (Option (Option S)))
          (StableArity.option (StableArity.double_option_iff.mpr h))
          (StableArity.double_option_iff.mpr h.option) (forgetNonseparatingEquiv S).symm
          (C.forget g (Option (Option S)) (StableArity.double_option_iff.mpr h) x))
  /-- Each component contributes once, even when the two outputs coincide. -/
  separating : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (x : C.H g₁ (Option S)) (y : C.H g₂ (Option T)),
    C.forget (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
        (F.push g₁ g₂ S T h₁ h₂ (x ⊗ₜ[R] y)) =
      C.rename (g₁ + g₂) (Option S ⊕ T) (Option (S ⊕ T))
        (StableArity.separating h₁.option h₂) (StableArity.separating h₁ h₂).option
        (optionSumEquivLeft S T).symm
        (F.push g₁ g₂ (Option S) T h₁.option h₂
          ((C.rename g₁ (Option (Option S)) (Option (Option S)) h₁.option h₁.option
            (swapDoubleOption S) (C.forget g₁ (Option S) h₁ x)) ⊗ₜ[R] y)) +
      C.rename (g₁ + g₂) (S ⊕ Option T) (Option (S ⊕ T))
        (StableArity.separating h₁ h₂.option) (StableArity.separating h₁ h₂).option
        (optionSumEquivRight S T).symm
        (F.push g₁ g₂ S (Option T) h₁ h₂.option
          (x ⊗ₜ[R] C.rename g₂ (Option (Option T)) (Option (Option T)) h₂.option h₂.option
            (swapDoubleOption T) (C.forget g₂ (Option T) h₂ y)))

end AxiomaticGW
