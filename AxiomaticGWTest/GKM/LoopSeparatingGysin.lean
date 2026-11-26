/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeLoopSeparatingProduct

/-! Nonunit and ordered-label consumers for the two disjoint-node maps. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.LoopSeparatingGysin

open AxiomaticGW AxiomaticGW.GKM.LoopSeparatingGysin
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- On Mbar(0,4), the first retained loop psi moves through the inverse cycle. -/
theorem left_nonunit_psi (P : PsiClasses C) :
    leftOtherPull C (P.psi 1 LoopLabels loopStable none) =
      P.psi 0 LeftNormalization leftStable none ⊗ₜ[R] 1 := by
  have ht : (leftOtherTransport C).symm (P.psi 1 LoopLabels loopStable none) =
      P.psi 1 (LoopLabels ⊕ Fin 0)
        (StableArity.separating leftStable unmarkedStable) (.inl none) := by
    apply (leftOtherTransport C).injective
    rw [AlgEquiv.apply_symm_apply]
    change _ = C.rename 1 (LoopLabels ⊕ Fin 0) LoopLabels
      (StableArity.separating leftStable unmarkedStable) loopStable leftOtherLabels _
    rw [P.rename_psi]
    rfl
  unfold leftOtherPull
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change Algebra.TensorProduct.map _ _
    (C.separating 0 1 LoopLabels (Fin 0) leftStable unmarkedStable
      ((leftOtherTransport C).symm (P.psi 1 LoopLabels loopStable none))) = _
  rw [ht, P.separating_psi_left, Algebra.TensorProduct.map_tmul, map_one]
  change C.rename 0 LeftNormalization LeftNormalization leftStable leftStable
    (forgetNonseparatingEquiv (Fin 1)).symm
    (P.psi 0 LeftNormalization leftStable (some none)) ⊗ₜ[R] 1 = _
  rw [P.rename_psi]
  rfl

/-- Test Mbar(0,3) labels directly: positive psi tests could conceal the cycle. -/
theorem right_normalization_labels :
    (forgetNonseparatingEquiv (Fin 0)).symm none = some (some none) ∧
    (forgetNonseparatingEquiv (Fin 0)).symm (some none) = none ∧
    (forgetNonseparatingEquiv (Fin 0)).symm (some (some none)) = some none :=
  ⟨rfl, rfl, rfl⟩

/-- The old mark stays on the elliptic factor of the second correspondence. -/
theorem right_old_mark_psi (P : PsiClasses C) :
    rightOtherPull C (P.psi 1 LoopLabels loopStable (some (some 0))) =
      P.psi 1 (Option (Fin 1)) markedStable (some 0) ⊗ₜ[R] 1 := by
  have ht : (rightOtherTransport C).symm
      (P.psi 1 LoopLabels loopStable (some (some 0))) =
      P.psi 1 (Fin 1 ⊕ RightLabels)
        (StableArity.separating markedStable rightStable) (.inl 0) := by
    apply (rightOtherTransport C).injective
    rw [AlgEquiv.apply_symm_apply]
    change _ = C.rename 1 (Fin 1 ⊕ RightLabels) LoopLabels
      (StableArity.separating markedStable rightStable) loopStable rightOtherLabels _
    rw [P.rename_psi]
    rfl
  unfold rightOtherPull
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change Algebra.TensorProduct.map _ _
    (C.separating 1 0 (Fin 1) RightLabels markedStable rightStable
      ((rightOtherTransport C).symm
        (P.psi 1 LoopLabels loopStable (some (some 0))))) = _
  rw [ht, P.separating_psi_left, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem left_arbitrary_insertions (N : NonseparatingPushforward C I)
    (x : C.H 0 LeftNormalization) (y : C.H 1 (Option (Fin 0))) :
    leftPush N (x ⊗ₜ[R] y) = N.push 0 (Option (Fin 1)) markedStable x ⊗ₜ[R] y :=
  TensorProduct.map_tmul _ _ x y

theorem right_arbitrary_insertions (N : NonseparatingPushforward C I)
    (x : C.H 1 (Option (Fin 1))) (y : C.H 0 RightNormalization) :
    rightPush N (x ⊗ₜ[R] y) = x ⊗ₜ[R] N.push 0 (Option (Fin 0)) unmarkedStable y :=
  TensorProduct.map_tmul _ _ x y

/-- Projection retains independent arbitrary insertions on both original sources. -/
theorem arbitrary_insertions (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (H : MixedGysinCompatible N)
    (z : C.H 1 LoopLabels)
    (w : C.H 1 (Option (Fin 1)) ⊗[R] C.H 1 (Option (Fin 0))) :
    loopPush N z * separatingPush F w =
      separatingPush F ((leftPush N (leftOtherPull C z) +
        rightPush N (rightOtherPull C z)) * w) :=
  product_of_mixedGysin F N H z w

end AxiomaticGWTest.GKM.LoopSeparatingGysin
