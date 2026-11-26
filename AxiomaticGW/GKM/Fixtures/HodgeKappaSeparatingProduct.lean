/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.CohFT.ForgetfulSeparatingKappa
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization

/-!
# Four actual separating-kappa columns as two class products

The old marking remains on its original ordered component. The actual
positions 11,12,13,14 are bound separately; the two component contributions
for each marked boundary are then derived from universal proper composition
and the existing realization laws. No Hodge or boundary-excess identity is
assumed or concluded. The new proper composition input remains geometric.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeKappaSeparatingProduct

open AdmcyclesHodgeStrataCandidates TensorProduct

theorem markedStable : StableArity 1 (Option (Fin 1)) := by
  unfold StableArity
  decide

theorem unmarkedStable : StableArity 1 (Option (Fin 0)) := by
  unfold StableArity
  decide

noncomputable def markedKappa : TautologicalStratum 1 (Option (Fin 1)) :=
  TautologicalStratum.kappaGenerator 1 (Option (Fin 1)) markedStable 1

noncomputable def unmarkedKappa : TautologicalStratum 1 (Option (Fin 0)) :=
  TautologicalStratum.kappaGenerator 1 (Option (Fin 0)) unmarkedStable 1

noncomputable def markedUnit : TautologicalStratum 1 (Option (Fin 1)) :=
  TautologicalStratum.fundamental 1 (Option (Fin 1)) markedStable

noncomputable def unmarkedUnit : TautologicalStratum 1 (Option (Fin 0)) :=
  TautologicalStratum.fundamental 1 (Option (Fin 0)) unmarkedStable

private theorem kappaVector_one :
    DecoratedStableGraph.kappaVector 4 (![1, 0, 0, 0] : Fin 4 → ℕ) =
      (Finsupp.single 1 1 : ℕ+ →₀ ℕ) := by
  have hcoordinates :
      (fun i : Fin 4 ↦ (Finsupp.single 1 1 : ℕ+ →₀ ℕ)
        (DecoratedStableGraph.kappaIndex 4 i)) = ![1, 0, 0, 0] := by
    funext i
    fin_cases i
    · exact Finsupp.single_eq_same
    · exact Finsupp.single_eq_of_ne (by decide)
    · exact Finsupp.single_eq_of_ne (by decide)
    · exact Finsupp.single_eq_of_ne (by decide)
  rw [← hcoordinates]
  apply DecoratedStableGraph.kappaVector_truncate
  intro i hi
  apply Finsupp.single_eq_of_ne
  intro heq
  subst i
  norm_num at hi

theorem rawGraph13_eq_marked_first :
    rawGraph13 = (markedKappa.separating unmarkedUnit).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1) := by
  dsimp only [markedKappa, TautologicalStratum.kappaGenerator]
  rw [← kappaVector_one]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

theorem rawGraph26_eq_unmarked_second :
    rawGraph26 = (markedUnit.separating unmarkedKappa).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1) := by
  dsimp only [unmarkedKappa, TautologicalStratum.kappaGenerator]
  rw [← kappaVector_one]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

theorem rawGraph14_eq_unmarked_first :
    rawGraph14 = (unmarkedKappa.separating markedUnit).relabel
      (finSumFinEquiv : Fin 0 ⊕ Fin 1 ≃ Fin 1) := by
  dsimp only [unmarkedKappa, TautologicalStratum.kappaGenerator]
  rw [← kappaVector_one]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

theorem rawGraph27_eq_marked_second :
    rawGraph27 = (unmarkedUnit.separating markedKappa).relabel
      (finSumFinEquiv : Fin 0 ⊕ Fin 1 ≃ Fin 1) := by
  dsimp only [markedKappa, TautologicalStratum.kappaGenerator]
  rw [← kappaVector_one]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Both actual kappa placements for the old marking on the left component
sum to a derived kappa-times-boundary class product. -/
theorem map_left_pair_eq_kappa_mul_boundary
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (Q : ForgetfulSeparatingComposition Fforget F)
    (H : GluingForgetfulCompatibility F N)
    (hκM : (A 1 (Option (Fin 1))).KappaForgetfulCompatible
      (A 1 (Option (Option (Fin 1)))) Fforget markedStable 1)
    (hκU : (A 1 (Option (Fin 0))).KappaForgetfulCompatible
      (A 1 (Option (Option (Fin 0)))) Fforget unmarkedStable 1)
    (hpsiM : (A 1 (Option (Option (Fin 1)))).LegPsiCompatible P markedStable.option)
    (hpsiU : (A 1 (Option (Option (Fin 0)))).LegPsiCompatible P unmarkedStable.option)
    (hfundM : (A 1 (Option (Option (Fin 1)))).map
      (StrataModule.basis (TautologicalStratum.fundamental 1
        (Option (Option (Fin 1))) markedStable.option)) = 1)
    (hfundU : (A 1 (Option (Option (Fin 0)))).map
      (StrataModule.basis (TautologicalStratum.fundamental 1
        (Option (Option (Fin 0))) unmarkedStable.option)) = 1)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N) :
    (A 2 (Fin 1)).map (StrataModule.basis rawGraph13) +
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph26) =
      P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) := by
  have hkM : (A 1 (Option (Fin 1))).map (StrataModule.basis markedKappa) =
      P.kappa Fforget 1 (Option (Fin 1)) markedStable 1 :=
    (A 1 (Option (Fin 1))).map_kappaGenerator
      (A 1 (Option (Option (Fin 1)))) Fforget P markedStable 1 hκM hpsiM hfundM
  have hkU : (A 1 (Option (Fin 0))).map (StrataModule.basis unmarkedKappa) =
      P.kappa Fforget 1 (Option (Fin 0)) unmarkedStable 1 :=
    (A 1 (Option (Fin 0))).map_kappaGenerator
      (A 1 (Option (Option (Fin 0)))) Fforget P unmarkedStable 1 hκU hpsiU hfundU
  let ρ := C.rename 2 (Fin 1 ⊕ Fin 0) (Fin 1)
    (StableArity.separating markedStable unmarkedStable) HodgeDegreeOneRealization.stable
    (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)
  have hp := congrArg ρ
    (Q.kappa_mul_push P N H 1 1 (Fin 1) (Fin 0) markedStable unmarkedStable 1 1 1)
  rw [map_mul ρ, P.kappa_rename, map_add ρ] at hp
  simp only [mul_one] at hp
  rw [rawGraph13_eq_marked_first, rawGraph26_eq_unmarked_second, hsep.2 _, hsep.2 _,
    hsep.1.2.2 _ _, hsep.1.2.2 _ _, hkM, hkU]
  dsimp only [markedUnit, unmarkedUnit]
  rw [hsep.1.1, hsep.1.2.1,
    HodgeDegreeOneRealization.rawGraph4_eq_left,
    HodgeDegreeOneRealization.separatingMarkedLeft.map_stratum_eq_classValue A F N hsep]
  exact hp.symm

/-- Both actual kappa placements for the old marking on the right component
sum to a derived kappa-times-boundary class product. -/
theorem map_right_pair_eq_kappa_mul_boundary
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (Q : ForgetfulSeparatingComposition Fforget F)
    (H : GluingForgetfulCompatibility F N)
    (hκM : (A 1 (Option (Fin 1))).KappaForgetfulCompatible
      (A 1 (Option (Option (Fin 1)))) Fforget markedStable 1)
    (hκU : (A 1 (Option (Fin 0))).KappaForgetfulCompatible
      (A 1 (Option (Option (Fin 0)))) Fforget unmarkedStable 1)
    (hpsiM : (A 1 (Option (Option (Fin 1)))).LegPsiCompatible P markedStable.option)
    (hpsiU : (A 1 (Option (Option (Fin 0)))).LegPsiCompatible P unmarkedStable.option)
    (hfundM : (A 1 (Option (Option (Fin 1)))).map
      (StrataModule.basis (TautologicalStratum.fundamental 1
        (Option (Option (Fin 1))) markedStable.option)) = 1)
    (hfundU : (A 1 (Option (Option (Fin 0)))).map
      (StrataModule.basis (TautologicalStratum.fundamental 1
        (Option (Option (Fin 0))) unmarkedStable.option)) = 1)
    (hsep : HodgeDegreeOneRealization.separatingMarkedRight.Compatible A F N) :
    (A 2 (Fin 1)).map (StrataModule.basis rawGraph14) +
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph27) =
      P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph5) := by
  have hkM : (A 1 (Option (Fin 1))).map (StrataModule.basis markedKappa) =
      P.kappa Fforget 1 (Option (Fin 1)) markedStable 1 :=
    (A 1 (Option (Fin 1))).map_kappaGenerator
      (A 1 (Option (Option (Fin 1)))) Fforget P markedStable 1 hκM hpsiM hfundM
  have hkU : (A 1 (Option (Fin 0))).map (StrataModule.basis unmarkedKappa) =
      P.kappa Fforget 1 (Option (Fin 0)) unmarkedStable 1 :=
    (A 1 (Option (Fin 0))).map_kappaGenerator
      (A 1 (Option (Option (Fin 0)))) Fforget P unmarkedStable 1 hκU hpsiU hfundU
  let ρ := C.rename 2 (Fin 0 ⊕ Fin 1) (Fin 1)
    (StableArity.separating unmarkedStable markedStable) HodgeDegreeOneRealization.stable
    (finSumFinEquiv : Fin 0 ⊕ Fin 1 ≃ Fin 1)
  have hp := congrArg ρ
    (Q.kappa_mul_push P N H 1 1 (Fin 0) (Fin 1) unmarkedStable markedStable 1 1 1)
  rw [map_mul ρ, P.kappa_rename, map_add ρ] at hp
  simp only [mul_one] at hp
  rw [rawGraph14_eq_unmarked_first, rawGraph27_eq_marked_second, hsep.2 _, hsep.2 _,
    hsep.1.2.2 _ _, hsep.1.2.2 _ _, hkM, hkU]
  dsimp only [markedUnit, unmarkedUnit]
  rw [hsep.1.1, hsep.1.2.1,
    HodgeDegreeOneRealization.rawGraph5_eq_right,
    HodgeDegreeOneRealization.separatingMarkedRight.map_stratum_eq_classValue A F N hsep]
  exact hp.symm

end AxiomaticGW.GKM.HodgeKappaSeparatingProduct
