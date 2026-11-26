/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeKappaLoopProduct

/-! Public source-binding and empty-label consumers of the conditional kappa product. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.HodgeKappaLoopProduct

open AxiomaticGW AdmcyclesHodgeStrataCandidates

theorem exact_position10 : raw_1_1_degree2Columns 10 = rawGraph17 := rfl

theorem actual_mixed_coefficient :
    raw_1_1_degree2Coordinates 10 =
      2 * raw_0_1_degree1Coordinates 1 * raw_0_1_degree1Coordinates 2 := by
  decide +kernel

theorem transport_new_marking (S : Type) :
    (forgetNonseparatingEquiv S).symm none = some (some none) := rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

theorem empty_labels_all_exponents
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (T : ForgetfulNonseparatingComposition Fforget N)
    (H : GluingForgetfulCompatibility F N) (m : ℕ)
    (x : C.H 1 (Option (Option (Fin 0)))) :
    P.kappa Fforget 2 (Fin 0) (by unfold StableArity; decide) m *
        N.push 1 (Fin 0) (by unfold StableArity; decide) x =
      N.push 1 (Fin 0) (by unfold StableArity; decide)
        (P.kappa Fforget 1 (Option (Option (Fin 0)))
          (by unfold StableArity; decide) m * x) :=
  T.kappa_mul_push P F H 1 (Fin 0) (by unfold StableArity; decide) m x

end AxiomaticGWTest.GKM.HodgeKappaLoopProduct
