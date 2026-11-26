/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeLoopSquare

/-! Nonunit tests expose the two label exchanges that unit specialization hides. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.LoopSquareGysin

open AxiomaticGW AxiomaticGW.GKM.LoopSquareGysin
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- The right double-loop pullback moves a source psi to the other glued pair. -/
theorem double_nonunit_psi (P : PsiClasses C) :
    doubleOtherPull C (P.psi 1 SourceLabels sourceStable none) =
      P.psi 0 DoubleLabels doubleStable none := by
  unfold doubleOtherPull
  rw [AlgHom.comp_apply, P.nonseparating_psi]
  change C.rename 0 DoubleLabels DoubleLabels doubleStable doubleStable pairExchange
    (P.psi 0 DoubleLabels doubleStable (some (some none))) = _
  rw [P.rename_psi]
  rfl

/-- Test rational labels directly: positive psi classes on Mbar(0,3) vanish,
so a psi-only consumer would not detect an omitted rational permutation. -/
theorem rational_node_labels :
    rationalExchange none = some 0 ∧ rationalExchange (some 0) = none ∧
      rationalExchange (some 1) = some 1 := by
  decide +kernel

/-- The elliptic retained branch is exchanged independently of the rational one. -/
theorem elliptic_nonunit_psi (P : PsiClasses C) :
    componentPull C (1 ⊗ₜ[R] P.psi 1 (Option (Fin 1)) ellipticStable (some 0)) =
      1 ⊗ₜ[R] P.psi 1 (Option (Fin 1)) ellipticStable none := by
  unfold componentPull
  rw [Algebra.TensorProduct.map_tmul, map_one]
  change 1 ⊗ₜ[R]
    C.rename 1 (Option (Fin 1)) (Option (Fin 1)) ellipticStable ellipticStable ellipticExchange
      (P.psi 1 (Option (Fin 1)) ellipticStable (some 0)) = _
  rw [P.rename_psi]
  rw [show ellipticExchange (some 0) = none by decide +kernel]

/-- The tensor operator retains arbitrary classes, not only component units. -/
theorem component_arbitrary_insertions
    (x : C.H 0 (Option (Fin 2))) (y : C.H 1 (Option (Fin 1))) :
    componentPull C (x ⊗ₜ[R] y) =
      C.rename 0 (Option (Fin 2)) (Option (Fin 2))
        rationalStable rationalStable rationalExchange x ⊗ₜ[R]
      C.rename 1 (Option (Fin 1)) (Option (Fin 1))
        ellipticStable ellipticStable ellipticExchange y := by
  unfold componentPull
  exact Algebra.TensorProduct.map_tmul _ _ x y

/-- Projection reduction retains two independent source insertions. -/
theorem arbitrary_insertions (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F N P) (x y : C.H 1 SourceLabels) :
    outerPush N x * outerPush N y = outerPush N (refinementOperator F N P x * y) :=
  product_of_selfGysin F N P H x y

end AxiomaticGWTest.GKM.LoopSquareGysin
