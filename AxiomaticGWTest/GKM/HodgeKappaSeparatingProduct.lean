/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeKappaSeparatingProduct

/-! Actual four-column binding, marking transports, and empty-label consumers. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.HodgeKappaSeparatingProduct

open AxiomaticGW AdmcyclesHodgeStrataCandidates TensorProduct

theorem four_original_positions :
    raw11Degree2Columns 11 = rawGraph26 ∧
    raw11Degree2Columns 12 = rawGraph27 ∧
    raw11Degree2Columns 13 = rawGraph13 ∧
    raw11Degree2Columns 14 = rawGraph14 := ⟨rfl, rfl, rfl, rfl⟩

theorem four_mixed_weights :
    raw11Degree2Coordinates 11 =
        2 * raw01Degree1Coordinates 1 * raw01Degree1Coordinates 3 ∧
    raw11Degree2Coordinates 13 =
        2 * raw01Degree1Coordinates 1 * raw01Degree1Coordinates 3 ∧
    raw11Degree2Coordinates 12 =
        2 * raw01Degree1Coordinates 1 * raw01Degree1Coordinates 4 ∧
    raw11Degree2Coordinates 14 =
        2 * raw01Degree1Coordinates 1 * raw01Degree1Coordinates 4 := by
  decide +kernel

theorem left_new_marking (S T : Type) :
    (optionSumEquivLeft S T).symm (.inl none) = none := rfl

theorem right_new_marking (S T : Type) :
    (optionSumEquivRight S T).symm (.inr none) = none := rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

theorem empty_labels_all_exponents
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (Q : ForgetfulSeparatingComposition Fforget F)
    (H : GluingForgetfulCompatibility F N) (m : ℕ)
    (x y : C.H 1 (Option (Fin 0))) :
    P.kappa Fforget 2 (Fin 0 ⊕ Fin 0) (by unfold StableArity; decide) m *
        F.push 1 1 (Fin 0) (Fin 0) (by unfold StableArity; decide)
          (by unfold StableArity; decide) (x ⊗ₜ[R] y) =
      F.push 1 1 (Fin 0) (Fin 0) (by unfold StableArity; decide)
        (by unfold StableArity; decide)
        ((P.kappa Fforget 1 (Option (Fin 0)) (by unfold StableArity; decide) m * x) ⊗ₜ[R] y) +
      F.push 1 1 (Fin 0) (Fin 0) (by unfold StableArity; decide)
        (by unfold StableArity; decide)
        (x ⊗ₜ[R] (P.kappa Fforget 1 (Option (Fin 0)) (by unfold StableArity; decide) m * y)) :=
  Q.kappa_mul_push P N H 1 1 (Fin 0) (Fin 0)
    (by unfold StableArity; decide) (by unfold StableArity; decide) m x y

end AxiomaticGWTest.GKM.HodgeKappaSeparatingProduct
