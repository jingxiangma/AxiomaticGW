/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSeparatingGysin

/-!
# The marked separating self-pull-push correspondences

The source is the ordered marked/unmarked elliptic product. The shared-node
correspondence has its negative cotangent normal factor. The disjoint source
is a rational three-marked central component and two ordered elliptic tails.
Its other contraction exchanges both tails and the two central node markings.

All operators act on arbitrary classes. `SelfGysinCompatible` remains an
explicit uninstantiated geometric excess/base-change input. The raw disjoint
map has coefficient one; no automorphism divisor is added to pushforward.
The constructed graph bindings do not prove the geometric fibre-product law.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.SeparatingSquareGysin

open LoopSeparatingGysin
open scoped TensorProduct

abbrev MarkedLabels := Option (Fin 1)
abbrev UnmarkedLabels := Option (Fin 0)
abbrev CentralLabels := Option (Option (Fin 1))

theorem centralStable : StableArity 0 CentralLabels := by
  unfold StableArity
  decide

/-- Internal node, external node, old marking, in that order. -/
def centralExchange : CentralLabels ≃ CentralLabels := Equiv.swap none (some none)

theorem centralExchange_labels :
    centralExchange none = some none ∧ centralExchange (some none) = none ∧
      centralExchange (some (some 0)) = some (some 0) := by
  decide +kernel

/-- The internal gluing retains the external node and the old marking. -/
def innerLabels : MarkedLabels ⊕ Fin 0 ≃ MarkedLabels where
  toFun := Sum.elim id Fin.elim0
  invFun := Sum.inl
  left_inv x := by
    rcases x with t | e
    · rfl
    · exact Fin.elim0 e
  right_inv _ := rfl

theorem innerLabels_values :
    innerLabels (.inl none) = none ∧ innerLabels (.inl (some 0)) = some 0 :=
  ⟨rfl, rfl⟩

def innerExpression : GluingExpression 1 MarkedLabels :=
  ((GluingExpression.fundamental 0 CentralLabels centralStable).separating
    (GluingExpression.fundamental 1 UnmarkedLabels unmarkedStable)).relabel innerLabels

def chainExpression : GluingExpression 2 (Fin 1) :=
  (innerExpression.separating
    (GluingExpression.fundamental 1 UnmarkedLabels unmarkedStable)).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

abbrev Source (C : StableCurveCohomology R) :=
  C.H 1 MarkedLabels ⊗[R] C.H 1 UnmarkedLabels
abbrev Refinement (C : StableCurveCohomology R) :=
  C.H 0 CentralLabels ⊗[R] (C.H 1 UnmarkedLabels ⊗[R] C.H 1 UnmarkedLabels)

def innerTransport (C : StableCurveCohomology R) :
    C.H 1 (MarkedLabels ⊕ Fin 0) ≃ₐ[R] C.H 1 MarkedLabels :=
  C.rename 1 (MarkedLabels ⊕ Fin 0) MarkedLabels
    (StableArity.separating centralStable unmarkedStable) markedStable innerLabels

def innerPush (F : SeparatingPushforward C I) :
    (C.H 0 CentralLabels ⊗[R] C.H 1 UnmarkedLabels) →ₗ[R] C.H 1 MarkedLabels :=
  (innerTransport C).toLinearMap.comp
    (F.push 0 1 MarkedLabels (Fin 0) centralStable unmarkedStable)

def innerPull (C : StableCurveCohomology R) :
    C.H 1 MarkedLabels →ₐ[R] (C.H 0 CentralLabels ⊗[R] C.H 1 UnmarkedLabels) :=
  (C.separating 0 1 MarkedLabels (Fin 0) centralStable unmarkedStable).comp
    (innerTransport C).symm.toAlgHom

/-- Associate first so the two elliptic factors are explicitly adjacent. -/
def refinementAssoc (C : StableCurveCohomology R) :
    ((C.H 0 CentralLabels ⊗[R] C.H 1 UnmarkedLabels) ⊗[R] C.H 1 UnmarkedLabels) ≃ₐ[R]
      Refinement C :=
  Algebra.TensorProduct.assoc R R R _ _ _

def refinementPush (F : SeparatingPushforward C I) : Refinement C →ₗ[R] Source C :=
  (TensorProduct.map (innerPush F) LinearMap.id).comp
    (refinementAssoc C).symm.toLinearMap

def refinementPull (C : StableCurveCohomology R) : Source C →ₐ[R] Refinement C :=
  (refinementAssoc C).toAlgHom.comp
    (Algebra.TensorProduct.map (innerPull C) (AlgHom.id R (C.H 1 UnmarkedLabels)))

/-- Swap the two elliptic factors and their central attachment labels together. -/
def refinementExchange (C : StableCurveCohomology R) : Refinement C →ₐ[R] Refinement C :=
  Algebra.TensorProduct.map
    (C.rename 0 CentralLabels CentralLabels centralStable centralStable centralExchange).toAlgHom
    (Algebra.TensorProduct.comm R (C.H 1 UnmarkedLabels)
      (C.H 1 UnmarkedLabels)).toAlgHom

def refinementOtherPull (C : StableCurveCohomology R) : Source C →ₐ[R] Refinement C :=
  (refinementExchange C).comp (refinementPull C)

def normalClass (P : PsiClasses C) : Source C :=
  -(P.psi 1 MarkedLabels markedStable none ⊗ₜ[R] 1 +
    1 ⊗ₜ[R] P.psi 1 UnmarkedLabels unmarkedStable none)

/-- The actual ordered disjoint-node contraction retains arbitrary decorations. -/
theorem refinementPush_tmul (F : SeparatingPushforward C I)
    (a : C.H 0 CentralLabels) (b c : C.H 1 UnmarkedLabels) :
    refinementPush F (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = innerPush F (a ⊗ₜ[R] b) ⊗ₜ[R] c := by
  unfold refinementPush
  rw [LinearMap.comp_apply]
  change TensorProduct.map _ _ ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = _
  exact TensorProduct.map_tmul _ _ _ _

theorem refinementExchange_tmul (a : C.H 0 CentralLabels)
    (b c : C.H 1 UnmarkedLabels) :
    refinementExchange C (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      C.rename 0 CentralLabels CentralLabels centralStable centralStable centralExchange a ⊗ₜ[R]
        (c ⊗ₜ[R] b) := by
  unfold refinementExchange
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- Genuine all-source self-pull-push input; no boundary product is a premise. -/
def SelfGysinCompatible (F : SeparatingPushforward C I) (P : PsiClasses C) : Prop :=
  (separatingPull C).toLinearMap.comp (separatingPush F) =
    LinearMap.mulRight R (normalClass P) +
      (refinementPush F).comp (refinementOtherPull C).toLinearMap

theorem selfGysin_apply (F : SeparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F P) (z : Source C) :
    separatingPull C (separatingPush F z) =
      z * normalClass P + refinementPush F (refinementOtherPull C z) :=
  congrArg (fun f : Source C →ₗ[R] Source C ↦ f z) H

theorem product_of_selfGysin (F : SeparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F P) (z w : Source C) :
    separatingPush F z * separatingPush F w =
      separatingPush F ((z * normalClass P +
        refinementPush F (refinementOtherPull C z)) * w) := by
  rw [separating_projection, selfGysin_apply F P H]

/-- A raw unit square follows from the operator input and existing projection. -/
theorem raw_separating_square (F : SeparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F P) :
    separatingPush F 1 ^ 2 =
      separatingPush F (normalClass P) + separatingPush F (refinementPush F 1) := by
  rw [pow_two, product_of_selfGysin F P H]
  simp only [map_one, one_mul, mul_one, map_add]

end AxiomaticGW.GKM.SeparatingSquareGysin
