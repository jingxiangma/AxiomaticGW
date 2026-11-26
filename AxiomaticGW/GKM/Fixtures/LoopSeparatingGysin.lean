/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization

/-!
# Two transverse correspondences for a loop and a marked separating boundary

The two source spaces normalize the loop on the marked or unmarked component.
Their other maps use separating pullback and the inverse existing three-mark
cycle, preserving the old marking. All maps act on arbitrary source classes.

`MixedGysinCompatible` is an explicit new geometric base-change obligation,
not a supplied product value or an instantiated model. The two retained edges
are disjoint, so this proposed transverse comparison has no excess factor.
A shared retained edge would have to give both separating and nonseparating
one-edge targets, which is impossible. This motivates the two disjoint cases;
no independent exhaustive enumeration is asserted here. The moduli fibre-product
interpretation and its completeness remain part of the geometric obligation.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSeparatingGysin

open scoped TensorProduct

abbrev LoopLabels := Option (Option (Fin 1))
abbrev RightLabels := Option (Option (Fin 0))
abbrev LeftNormalization := Option (Option (Option (Fin 1)))
abbrev RightNormalization := Option (Option (Option (Fin 0)))

theorem markedStable : StableArity 1 (Option (Fin 1)) := by
  unfold StableArity
  decide

theorem unmarkedStable : StableArity 1 (Option (Fin 0)) := by
  unfold StableArity
  decide

theorem loopStable : StableArity 1 LoopLabels :=
  StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable

theorem leftStable : StableArity 0 LeftNormalization :=
  StableArity.double_option_iff.mpr markedStable

theorem rightStable : StableArity 0 RightNormalization :=
  StableArity.double_option_iff.mpr unmarkedStable

/-- In the first refinement all three surviving labels lie on the rational side. -/
def leftOtherLabels : LoopLabels ⊕ Fin 0 ≃ LoopLabels where
  toFun := Sum.elim id Fin.elim0
  invFun := Sum.inl
  left_inv x := by
    rcases x with t | e
    · rfl
    · exact Fin.elim0 e
  right_inv _ := rfl

/-- In the second refinement the old mark lies on the elliptic side. -/
def rightOtherLabels : Fin 1 ⊕ RightLabels ≃ LoopLabels where
  toFun
    | .inl s => some (some s)
    | .inr none => none
    | .inr (some none) => some none
    | .inr (some (some e)) => Fin.elim0 e
  invFun
    | none => .inr none
    | some none => .inr (some none)
    | some (some s) => .inl s
  left_inv x := by
    rcases x with s | (_ | (_ | e))
    · rfl
    · rfl
    · rfl
    · exact Fin.elim0 e
  right_inv x := by rcases x with _ | (_ | s) <;> rfl

/-- The old label and both loop branches have explicit ordered source images. -/
theorem retained_label_bindings :
    leftOtherLabels (.inl none) = none ∧
    leftOtherLabels (.inl (some none)) = some none ∧
    leftOtherLabels (.inl (some (some 0))) = some (some 0) ∧
    rightOtherLabels (.inr none) = none ∧
    rightOtherLabels (.inr (some none)) = some none ∧
    rightOtherLabels (.inl 0) = some (some 0) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Convert canonical separating order (node,a,b,old) to (a,b,node,old). -/
theorem normalization_cycle (S : Type) :
    (forgetNonseparatingEquiv S).symm none = some (some none) ∧
    (forgetNonseparatingEquiv S).symm (some none) = none ∧
    (forgetNonseparatingEquiv S).symm (some (some none)) = some none ∧
    (∀ s : S, (forgetNonseparatingEquiv S).symm (some (some (some s))) =
      some (some (some s))) := ⟨rfl, rfl, rfl, fun _ ↦ rfl⟩

/-- Normalize the loop on the component that retains the old marking. -/
def leftRefinement : GluingExpression 2 (Fin 1) :=
  ((GluingExpression.fundamental 0 LeftNormalization leftStable).nonseparating.separating
    (GluingExpression.fundamental 1 (Option (Fin 0)) unmarkedStable)).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)

/-- Normalize the loop on the component without the old marking. -/
def rightRefinement : GluingExpression 2 (Fin 1) :=
  ((GluingExpression.fundamental 1 (Option (Fin 1)) markedStable).separating
    (GluingExpression.fundamental 0 RightNormalization rightStable).nonseparating).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

def separatingTransport (C : StableCurveCohomology R) :
    C.H 2 (Fin 1 ⊕ Fin 0) ≃ₐ[R] C.H 2 (Fin 1) :=
  C.rename 2 (Fin 1 ⊕ Fin 0) (Fin 1)
    (StableArity.separating markedStable unmarkedStable) HodgeDegreeOneRealization.stable
    (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)

def separatingPush (F : SeparatingPushforward C I) :
    (C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) →ₗ[R] C.H 2 (Fin 1) :=
  (separatingTransport C).toLinearMap.comp
    (F.push 1 1 (Fin 1) (Fin 0) markedStable unmarkedStable)

def separatingPull (C : StableCurveCohomology R) :
    C.H 2 (Fin 1) →ₐ[R] (C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) :=
  (C.separating 1 1 (Fin 1) (Fin 0) markedStable unmarkedStable).comp
    (separatingTransport C).symm.toAlgHom

def loopPush (N : NonseparatingPushforward C I) :
    C.H 1 LoopLabels →ₗ[R] C.H 2 (Fin 1) :=
  N.push 1 (Fin 1) HodgeDegreeOneRealization.stable

def leftPush (N : NonseparatingPushforward C I) :
    (C.H 0 LeftNormalization ⊗[R] C.H 1 (Option (Fin 0))) →ₗ[R]
      (C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) :=
  TensorProduct.map (N.push 0 (Option (Fin 1)) markedStable) LinearMap.id

def rightPush (N : NonseparatingPushforward C I) :
    (C.H 1 (Option (Fin 1)) ⊗[R] C.H 0 RightNormalization) →ₗ[R]
      (C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) :=
  TensorProduct.map LinearMap.id (N.push 0 (Option (Fin 0)) unmarkedStable)

def leftOtherTransport (C : StableCurveCohomology R) :
    C.H 1 (LoopLabels ⊕ Fin 0) ≃ₐ[R] C.H 1 LoopLabels :=
  C.rename 1 (LoopLabels ⊕ Fin 0) LoopLabels
    (StableArity.separating leftStable unmarkedStable) loopStable leftOtherLabels

def rightOtherTransport (C : StableCurveCohomology R) :
    C.H 1 (Fin 1 ⊕ RightLabels) ≃ₐ[R] C.H 1 LoopLabels :=
  C.rename 1 (Fin 1 ⊕ RightLabels) LoopLabels
    (StableArity.separating markedStable rightStable) loopStable rightOtherLabels

/-- The right-hand map glues the separating edge and retains the two ordered loop flags. -/
def leftOtherPull (C : StableCurveCohomology R) :
    C.H 1 LoopLabels →ₐ[R]
      (C.H 0 LeftNormalization ⊗[R] C.H 1 (Option (Fin 0))) :=
  (Algebra.TensorProduct.map
    (C.rename 0 LeftNormalization LeftNormalization leftStable leftStable
      (forgetNonseparatingEquiv (Fin 1)).symm).toAlgHom
    (AlgHom.id R (C.H 1 (Option (Fin 0))))).comp
    ((C.separating 0 1 LoopLabels (Fin 0) leftStable unmarkedStable).comp
      (leftOtherTransport C).symm.toAlgHom)

/-- The analogous map rotates only the unmarked rational normalization factor. -/
def rightOtherPull (C : StableCurveCohomology R) :
    C.H 1 LoopLabels →ₐ[R]
      (C.H 1 (Option (Fin 1)) ⊗[R] C.H 0 RightNormalization) :=
  (Algebra.TensorProduct.map
    (AlgHom.id R (C.H 1 (Option (Fin 1))))
    (C.rename 0 RightNormalization RightNormalization rightStable rightStable
      (forgetNonseparatingEquiv (Fin 0)).symm).toAlgHom).comp
    ((C.separating 1 0 (Fin 1) RightLabels markedStable rightStable).comp
      (rightOtherTransport C).symm.toAlgHom)

/-- Explicit two-component, arbitrary-class transverse Gysin obligation.
No unit or desired boundary product occurs in this map equality. -/
def MixedGysinCompatible (N : NonseparatingPushforward C I) : Prop :=
  (separatingPull C).toLinearMap.comp (loopPush N) =
    (leftPush N).comp (leftOtherPull C).toLinearMap +
      (rightPush N).comp (rightOtherPull C).toLinearMap

theorem mixedGysin_apply (N : NonseparatingPushforward C I) (H : MixedGysinCompatible N)
    (z : C.H 1 LoopLabels) :
    separatingPull C (loopPush N z) =
      leftPush N (leftOtherPull C z) + rightPush N (rightOtherPull C z) :=
  congrArg (fun f : C.H 1 LoopLabels →ₗ[R]
    (C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) ↦ f z) H

/-- Projection survives the actual retained-label equivalence. -/
theorem separating_projection (F : SeparatingPushforward C I)
    (x : C.H 2 (Fin 1)) (w : C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) :
    x * separatingPush F w = separatingPush F (separatingPull C x * w) := by
  change x * separatingTransport C (F.push 1 1 (Fin 1) (Fin 0)
      markedStable unmarkedStable w) =
    separatingTransport C (F.push 1 1 (Fin 1) (Fin 0) markedStable unmarkedStable
      (C.separating 1 1 (Fin 1) (Fin 0) markedStable unmarkedStable
        ((separatingTransport C).symm x) * w))
  rw [F.projection_formula, map_mul, AlgEquiv.apply_symm_apply]

theorem leftPush_one (N : NonseparatingPushforward C I) :
    leftPush N 1 = N.push 0 (Option (Fin 1)) markedStable 1 ⊗ₜ[R] 1 :=
  TensorProduct.map_tmul _ _ 1 1

theorem rightPush_one (N : NonseparatingPushforward C I) :
    rightPush N 1 = 1 ⊗ₜ[R] N.push 0 (Option (Fin 0)) unmarkedStable 1 :=
  TensorProduct.map_tmul _ _ 1 1

/-- Arbitrary source insertions remain visible until the unit specialization. -/
theorem product_of_mixedGysin (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (H : MixedGysinCompatible N)
    (z : C.H 1 LoopLabels)
    (w : C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) :
    loopPush N z * separatingPush F w =
      separatingPush F ((leftPush N (leftOtherPull C z) +
        rightPush N (rightOtherPull C z)) * w) := by
  rw [separating_projection, mixedGysin_apply N H]

/-- The two actual boundary constructions are obtained only after specializing to units. -/
theorem unit_product (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (H : MixedGysinCompatible N) :
    loopPush N 1 * separatingPush F 1 =
      separatingPush F (N.push 0 (Option (Fin 1)) markedStable 1 ⊗ₜ[R] 1) +
        separatingPush F (1 ⊗ₜ[R] N.push 0 (Option (Fin 0)) unmarkedStable 1) := by
  rw [product_of_mixedGysin F N H]
  simp only [map_one, mul_one, map_add, leftPush_one, rightPush_one]

end AxiomaticGW.GKM.LoopSeparatingGysin
