/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeKappaCorolla

/-!
# Consumer checks for corolla forgetful realization

The original position-sixteen coefficient is retained in the finite source
identity. Empty retained labels test generator recovery and a two-factor
product with distinct positive indices. Every geometric law used by the
conditional class statement remains an explicit argument.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.CorollaForgetfulRealization

open AxiomaticGW AdmcyclesHodgeStrataCandidates

/-- The actual weighted packet column is the corrected finite pushforward,
without identifying its realization with a class until compatibility is given. -/
theorem weighted_actual_column :
    raw_1_1_degree2Coordinates 16 • StrataModule.basis (raw_1_1_degree2Columns 16) =
      (1 / 144 : ℚ) •
        (CorollaForgetful.push 2 (Fin 1) GKM.HodgeDegreeOneRealization.stable
          (Finsupp.single 1 1) 1 -
          StrataModule.basis (TautologicalStratum.kappaGenerator 2 (Fin 1)
            GKM.HodgeDegreeOneRealization.stable 2)) := by
  rw [GKM.HodgeKappaCorolla.actual_two_term_push, add_sub_cancel_right]
  rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Universal compatibility recovers every positive generator even with no
retained markings; no separate target-generator assumption is needed. -/
theorem empty_labels_generator_recovery
    (A : StrataRealization C 2 (Fin 0))
    (B : StrataRealization C 2 (Option (Fin 0)))
    (F : ForgetfulPushforward C I)
    (hc : A.CorollaForgetfulCompatible B F (by unfold StableArity; decide)) (b : ℕ+) :
    A.KappaForgetfulCompatible B F (by unfold StableArity; decide) b := hc.kappaGenerator b

/-- Distinct indices give the codimension-three product on the unmarked
stable genus-two space; the statement is not killed by its dimension bound. -/
theorem distinct_indices_empty_labels
    (A : StrataRealization C 2 (Fin 0))
    (B : StrataRealization C 2 (Option (Fin 0)))
    (D : StrataRealization C 2 (Option (Option (Fin 0))))
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Q : ForgetfulSquareCompatibility Fforget F)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (hc : A.CorollaForgetfulCompatible B Fforget (by unfold StableArity; decide))
    (hκ : B.KappaForgetfulCompatible D Fforget (by unfold StableArity; decide) 1)
    (hpsiB : B.LegPsiCompatible P (by unfold StableArity; decide))
    (hpsiD : D.LegPsiCompatible P (by unfold StableArity; decide))
    (hfundB : B.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Option (Fin 0)) (by unfold StableArity; decide))) = 1)
    (hfundD : D.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Option (Option (Fin 0)))
        (by unfold StableArity; decide))) = 1) :
    A.map (StrataModule.basis (TautologicalStratum.oneVertex 2 (Fin 0)
      (by unfold StableArity; decide)
      (Finsupp.single 1 1 + Finsupp.single 2 1) (fun _ ↦ 0))) =
      P.kappa Fforget 2 (Fin 0)
        (by unfold StableArity; decide) 1 * P.kappa Fforget 2 (Fin 0) (by unfold StableArity; decide) 2 :=
  A.map_two_kappa_corolla B D Fforget F N P K Q hK H
    (by unfold StableArity; decide) 1 2 hc hκ hpsiB hpsiD hfundB hfundD

end AxiomaticGWTest.GKM.CorollaForgetfulRealization
