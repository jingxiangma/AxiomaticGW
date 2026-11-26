/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.Ancestors
public import AxiomaticGW.Linear.SeparatingContraction

/-!
# Proper separating pushforward and boundary evaluation

The source is the ordered product of the two stable component spaces.
Product integration is the tensor product of their linear integration maps,
followed by multiplication in the coefficient ring. Projection and proper
integration laws are primitive geometric inputs; the CohFT contraction
equation is derived from them. Raw pushforward has no automorphism divisor.

Source psi powers, including the two node powers, give ancestor equations.
Stable-map descendant comparisons remain separate geometric obligations.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

universe u

namespace StableCurveIntegration

variable {R : Type u} [CommRing R] [Algebra ℚ R] {C : StableCurveCohomology R}

/-- The product integral is determined by the two linear factor integrals.
Neither factor integral is assumed multiplicative. -/
def tensorIntegral (I : StableCurveIntegration C)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ S) (h₂ : StableArity g₂ T) :
    (C.H g₁ S ⊗[R] C.H g₂ T) →ₗ[R] R :=
  (LinearMap.mul' R R).comp
    (TensorProduct.map (I.integrate g₁ S h₁) (I.integrate g₂ T h₂))

/-- Pure tensor integration multiplies the two separate integrals. -/
theorem tensorIntegral_tmul (I : StableCurveIntegration C)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ S) (h₂ : StableArity g₂ T)
    (x : C.H g₁ S) (y : C.H g₂ T) :
    I.tensorIntegral g₁ g₂ S T h₁ h₂ (x ⊗ₜ[R] y) =
      I.integrate g₁ S h₁ x * I.integrate g₂ T h₂ y := by
  rw [tensorIntegral, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]

/-- Multiplying by a pure decoration tensor scalarizes each factor with
its own decoration before multiplying their integrals. -/
theorem tensorIntegral_mul_tmul (I : StableCurveIntegration C)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ S) (h₂ : StableArity g₂ T)
    (x : C.H g₁ S) (y : C.H g₂ T) :
    (I.tensorIntegral g₁ g₂ S T h₁ h₂).comp (LinearMap.mulRight R (x ⊗ₜ[R] y)) =
      (LinearMap.mul' R R).comp (TensorProduct.map
        ((I.integrate g₁ S h₁).comp (LinearMap.mulRight R x))
        ((I.integrate g₂ T h₂).comp (LinearMap.mulRight R y))) := by
  apply TensorProduct.ext
  ext a b
  change I.tensorIntegral g₁ g₂ S T h₁ h₂ ((a ⊗ₜ[R] b) * (x ⊗ₜ[R] y)) =
    ((LinearMap.mul' R R).comp (TensorProduct.map
      ((I.integrate g₁ S h₁).comp (LinearMap.mulRight R x))
      ((I.integrate g₂ T h₂).comp (LinearMap.mulRight R y)))) (a ⊗ₜ[R] b)
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, tensorIntegral_tmul,
    TensorProduct.map_tmul, LinearMap.mul'_apply]

end StableCurveIntegration

/-- Primitive proper pushforward along separating gluing of two ordered
stable components. These are geometric inputs, independent of a class family. -/
structure SeparatingPushforward {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) (I : StableCurveIntegration C) where
  /-- The entire product cohomology is available as the source. -/
  push : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (_h₁ : StableArity g₁ (Option S)) (_h₂ : StableArity g₂ (Option T)),
    (C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) →ₗ[R] C.H (g₁ + g₂) (S ⊕ T)
  /-- Independent relabelling of the retained component markings is natural. -/
  push_rename : ∀ (g₁ g₂ : ℕ) (S T U W : Type)
      [Fintype S] [Fintype T] [Fintype U] [Fintype W]
      (hS : StableArity g₁ (Option S)) (hT : StableArity g₂ (Option T))
      (hU : StableArity g₁ (Option U)) (hW : StableArity g₂ (Option W))
      (e : S ≃ U) (f : T ≃ W)
      (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)),
    push g₁ g₂ U W hU hW (TensorProduct.map
        (C.rename g₁ (Option S) (Option U) hS hU e.optionCongr).toLinearMap
        (C.rename g₂ (Option T) (Option W) hT hW f.optionCongr).toLinearMap x) =
      C.rename (g₁ + g₂) (S ⊕ T) (U ⊕ W)
        (StableArity.separating hS hT) (StableArity.separating hU hW)
        (e.sumCongr f) (push g₁ g₂ S T hS hT x)
  /-- Exchanging the ordered components swaps the source tensor factors and
  transports the genus and retained labels in the target. -/
  push_swap : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)),
    push g₂ g₁ T S h₂ h₁ (TensorProduct.comm R _ _ x) =
      C.rename (g₂ + g₁) (S ⊕ T) (T ⊕ S)
        ((Nat.add_comm g₁ g₂) ▸ StableArity.separating h₁ h₂)
        (StableArity.separating h₂ h₁) (Equiv.sumComm S T)
        (EvenGradedAlgebra.congr
          (congrArg (fun k ↦ C.H k (S ⊕ T)) (Nat.add_comm g₁ g₂))
            (push g₁ g₂ S T h₁ h₂ x))
  /-- The boundary has codimension one in the glued moduli space. -/
  push_degree : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (d : ℕ) (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)),
    x ∈ tensorDegree (C.H g₁ (Option S)) (C.H g₂ (Option T)) d →
      push g₁ g₂ S T h₁ h₂ x ∈ (C.H (g₁ + g₂) (S ⊕ T)).degree (d + 1)
  /-- Projection formula using the existing product-valued pullback. -/
  projection_formula : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (x : C.H (g₁ + g₂) (S ⊕ T))
      (y : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)),
    push g₁ g₂ S T h₁ h₂ (C.separating g₁ g₂ S T h₁ h₂ x * y) =
      x * push g₁ g₂ S T h₁ h₂ y
  /-- Proper integration of raw pushforward is integration over the product. -/
  integrate_push : ∀ (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
      (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
      (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)),
    I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
        (push g₁ g₂ S T h₁ h₂ x) =
      I.tensorIntegral g₁ g₂ (Option S) (Option T) h₁ h₂ x

namespace SeparatingPushforward

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Evaluation against a pushed product class follows from the primitive
projection and integration formulas. -/
theorem integrate_mul_push (F : SeparatingPushforward C I)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (x : C.H (g₁ + g₂) (S ⊕ T))
    (y : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) :
    I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
        (x * F.push g₁ g₂ S T h₁ h₂ y) =
      I.tensorIntegral g₁ g₂ (Option S) (Option T) h₁ h₂
        (C.separating g₁ g₂ S T h₁ h₂ x * y) := by
  rw [← F.projection_formula, F.integrate_push]

end SeparatingPushforward

namespace CohFT

variable {R V : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- Integrate a CohFT class against raw proper pushforward of an arbitrary
product decoration, including combinations of pure tensors. -/
def separatingInvariant (Omega : CohFT R V C) (F : SeparatingPushforward C I)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) :
    MultilinearMap R (fun _ : S ⊕ T ↦ V) R :=
  ((I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)).comp
    (LinearMap.mulRight R (F.push g₁ g₂ S T h₁ h₂ x))).compMultilinearMap
      (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂))

/-- Evaluation uses the actual upper CohFT class and proper pushforward. -/
theorem separatingInvariant_apply (Omega : CohFT R V C) (F : SeparatingPushforward C I)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) (a : S ⊕ T → V) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ x a =
      I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
        (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) a *
          F.push g₁ g₂ S T h₁ h₂ x) := rfl

/-- For any product decoration, gluing evaluates the contracted component
classes against that same decoration and the product integral. -/
theorem separatingInvariant_eq_contraction (Omega : CohFT R V C)
    (F : SeparatingPushforward C I) (g₁ g₂ : ℕ) (S T : Type)
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (x : C.H g₁ (Option S) ⊗[R] C.H g₂ (Option T)) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ x =
      ((I.tensorIntegral g₁ g₂ (Option S) (Option T) h₁ h₂).comp
        (LinearMap.mulRight R x)).compMultilinearMap
          (Omega.pairing.pairContractTarget
            (Omega.omega g₁ (Option S) h₁) (Omega.omega g₂ (Option T) h₂)) := by
  ext a
  rw [separatingInvariant_apply, F.integrate_mul_push]
  have hglue := congrArg (fun f ↦ f a) (Omega.separating g₁ g₂ S T h₁ h₂)
  exact congrArg (fun y ↦ I.tensorIntegral g₁ g₂ (Option S) (Option T) h₁ h₂
    (y * x)) hglue.symm

/-- A pure decoration tensor separates the two linear component integrals
before inverse-metric contraction, without multiplicativity assumptions. -/
theorem separatingInvariant_tmul (Omega : CohFT R V C) (F : SeparatingPushforward C I)
    (g₁ g₂ : ℕ) (S T : Type) [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (x : C.H g₁ (Option S)) (y : C.H g₂ (Option T)) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ (x ⊗ₜ[R] y) =
      Omega.pairing.pairContract
        (((I.integrate g₁ (Option S) h₁).comp (LinearMap.mulRight R x)).compMultilinearMap
          (Omega.omega g₁ (Option S) h₁))
        (((I.integrate g₂ (Option T) h₂).comp (LinearMap.mulRight R y)).compMultilinearMap
          (Omega.omega g₂ (Option T) h₂)) := by
  rw [separatingInvariant_eq_contraction, I.tensorIntegral_mul_tmul,
    Omega.pairing.pairContractTarget_comp_map]

/-- Every component marking and both ordered node powers occur in the
ancestor contraction for a tensor product of source psi monomials. -/
theorem separatingInvariant_monomial (Omega : CohFT R V C) (P : PsiClasses C)
    (F : SeparatingPushforward C I) (g₁ g₂ : ℕ) (S T : Type)
    [Fintype S] [Fintype T]
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (k : Option S → ℕ) (l : Option T → ℕ) :
    Omega.separatingInvariant F g₁ g₂ S T h₁ h₂
        (P.monomial g₁ (Option S) h₁ k ⊗ₜ[R] P.monomial g₂ (Option T) h₂ l) =
      Omega.pairing.pairContract (Omega.ancestor P I g₁ (Option S) h₁ k)
        (Omega.ancestor P I g₂ (Option T) h₂ l) := by
  rw [separatingInvariant_tmul]
  rfl

end CohFT

end AxiomaticGW
