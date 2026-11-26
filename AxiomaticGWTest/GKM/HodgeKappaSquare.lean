/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeKappaSquare

/-! Actual source positions and coefficients, distinct kappa decorations,
ordered new markings, and the empty-label/index-zero boundary cases. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.HodgeKappaSquare

open AxiomaticGW AdmcyclesHodgeStrataCandidates

theorem actual_positions :
    raw_0_1_degree1Columns 1 = rawGraph2 ∧
    raw_1_1_degree2Columns 16 = rawGraph21 := ⟨rfl, rfl⟩

theorem actual_square_coefficient :
    raw_1_1_degree2Coordinates 16 = raw_0_1_degree1Coordinates 1 ^ 2 := by
  decide +kernel

theorem kappa_one_twice_ne_kappa_two :
    (Finsupp.single 1 2 : ℕ+ →₀ ℕ) ≠ Finsupp.single 2 1 := by
  intro heq
  have h := congrArg (fun f : ℕ+ →₀ ℕ ↦ f 1) heq
  norm_num only [Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (1 : ℕ+) ≠ 2)] at h

theorem exchanged_new_markings (S : Type) :
    swapDoubleOption S none = some none ∧
    swapDoubleOption S (some none) = none := ⟨rfl, rfl⟩

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

theorem empty_labels_index_zero
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Q : ForgetfulSquareCompatibility Fforget F)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C) :
    C.forget 2 (Fin 0) (by unfold StableArity; decide)
        (P.kappa Fforget 2 (Fin 0) (by unfold StableArity; decide) 0) =
      P.kappa Fforget 2 (Option (Fin 0)) (by unfold StableArity; decide) 0 - 1 := by
  simpa only [pow_zero] using
    Q.forget_kappa N P K hK H 2 (Fin 0) (by unfold StableArity; decide) 0

theorem empty_labels_two_indices
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Q : ForgetfulSquareCompatibility Fforget F)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C) (a b : ℕ) :
    Fforget.push 2 (Fin 0) (by unfold StableArity; decide)
        (P.kappa Fforget 2 (Option (Fin 0)) (by unfold StableArity; decide) a *
          P.psi 2 (Option (Fin 0)) (by unfold StableArity; decide) none ^ (b + 1)) =
      P.kappa Fforget 2 (Fin 0) (by unfold StableArity; decide) a *
        P.kappa Fforget 2 (Fin 0) (by unfold StableArity; decide) b +
      P.kappa Fforget 2 (Fin 0) (by unfold StableArity; decide) (a + b) :=
  Q.push_kappa_mul_newPsi N P K hK H 2 (Fin 0) (by unfold StableArity; decide) a b

end AxiomaticGWTest.GKM.HodgeKappaSquare
