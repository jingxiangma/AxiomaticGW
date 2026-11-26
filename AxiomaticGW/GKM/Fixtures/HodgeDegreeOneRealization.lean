/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates
public import AxiomaticGW.Tautological.KappaRealization
public import AxiomaticGW.Tautological.GluingForgetful
public import AxiomaticGW.Tautological.GraphIsomorphisms

/-!
# Realization of the actual five degree-one source terms

The five columns decoded from the admcycles packet are identified with the
external psi generator, the positive kappa generator, and three raw gluing
constructions. Their coefficients and both ordered separating occurrences are
retained. Existing primitive realization laws and the explicit kappa/forgetful
compatibility derive the complete image formula.

This does not identify that formula with a Hodge class or a GW class, prove a
product law, or construct a class-valued CohFT from numerical localization.
-/

@[expose] public section

namespace AxiomaticGW.GKM.HodgeDegreeOneRealization

open AdmcyclesHodgeStrataCandidates
open scoped BigOperators

universe u

/-- The single original marking is stable in genus two. -/
theorem stable : StableArity 2 (Fin 1) := by
  unfold StableArity
  decide

/-- The raw nonseparating boundary with its two node branches distinguished. -/
def loop : GluingExpression 2 (Fin 1) :=
  (GluingExpression.fundamental 1 (Option (Option (Fin 1)))
    (by unfold StableArity; decide)).nonseparating

/-- The ordered separating occurrence with the marking on the left. -/
def separatingMarkedLeft : GluingExpression 2 (Fin 1) :=
  ((GluingExpression.fundamental 1 (Option (Fin 1)) (by unfold StableArity; decide)).separating
    (GluingExpression.fundamental 1 (Option (Fin 0)) (by unfold StableArity; decide))).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1)

/-- The separately retained occurrence with the marking on the right. -/
def separatingMarkedRight : GluingExpression 2 (Fin 1) :=
  ((GluingExpression.fundamental 1 (Option (Fin 0)) (by unfold StableArity; decide)).separating
    (GluingExpression.fundamental 1 (Option (Fin 1)) (by unfold StableArity; decide))).relabel
      (finSumFinEquiv : Fin 0 ⊕ Fin 1 ≃ Fin 1)

/-- Bind the decoded external-psi column to the existing quotient operation. -/
theorem rawGraph1_eq_psi :
    rawGraph1 = (TautologicalStratum.fundamental 2 (Fin 1) stable).addLegPsi
      (fun _ ↦ 1) := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Bind the actual positive kappa index, rather than introducing a supplied class. -/
theorem rawGraph2_eq_kappa :
    rawGraph2 = TautologicalStratum.kappaGenerator 2 (Fin 1) stable 1 := by
  have hvector :
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
  change rawGraph2 = TautologicalStratum.oneVertex 2 (Fin 1) stable
    (Finsupp.single 1 1) (fun _ ↦ 0)
  rw [← hvector]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The loop column uses the raw gluing convention, with no added symmetry factor. -/
theorem rawGraph3_eq_loop : rawGraph3 = loop.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The first ordered separating column retains its marked component. -/
theorem rawGraph4_eq_left : rawGraph4 = separatingMarkedLeft.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The second ordered separating column retains its marked component. -/
theorem rawGraph5_eq_right : rawGraph5 = separatingMarkedRight.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Realize every actual degree-one source column under its primitive compatibility law. -/
theorem map_raw_degree_one
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fforget : ForgetfulPushforward C I)
    (Fsep : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C)
    (hbasePsi : (A 2 (Fin 1)).LegPsiCompatible P stable)
    (hbaseFund : (A 2 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1)
    (hnewPsi : (A 2 (Option (Fin 1))).LegPsiCompatible P stable.option)
    (hnewFund : (A 2 (Option (Fin 1))).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Option (Fin 1)) stable.option)) = 1)
    (hκ : (A 2 (Fin 1)).KappaForgetfulCompatible
      (A 2 (Option (Fin 1))) Fforget stable 1)
    (hloop : loop.Compatible A Fsep N)
    (hleft : separatingMarkedLeft.Compatible A Fsep N)
    (hright : separatingMarkedRight.Compatible A Fsep N) :
    (A 2 (Fin 1)).map raw_0_1_degree1 =
      (-1 / 12 : ℚ) • P.psi 2 (Fin 1) stable 0 +
      (1 / 12 : ℚ) • P.kappa Fforget 2 (Fin 1) stable 1 +
      (1 / 24 : ℚ) • loop.classValue Fsep N +
      (1 / 24 : ℚ) • separatingMarkedLeft.classValue Fsep N +
      (1 / 24 : ℚ) • separatingMarkedRight.classValue Fsep N := by
  have hpsi : (A 2 (Fin 1)).map (StrataModule.basis rawGraph1) =
      P.psi 2 (Fin 1) stable 0 := by
    rw [rawGraph1_eq_psi,
      (A 2 (Fin 1)).map_addLegPsi P stable hbasePsi, hbaseFund, one_mul]
    simp only [PsiClasses.monomial, Fin.prod_univ_one, pow_one]
  have hkappa : (A 2 (Fin 1)).map (StrataModule.basis rawGraph2) =
      P.kappa Fforget 2 (Fin 1) stable 1 := by
    rw [rawGraph2_eq_kappa]
    exact (A 2 (Fin 1)).map_kappaGenerator
      (A 2 (Option (Fin 1))) Fforget P stable 1 hκ hnewPsi hnewFund
  simp only [raw_0_1_degree1, RelationCertificate.interpret_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, raw_0_1_degree1Columns,
    raw_0_1_degree1Coordinates, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, map_add, map_smul, add_zero,
    hpsi, hkappa, rawGraph3_eq_loop, rawGraph4_eq_left, rawGraph5_eq_right,
    loop.map_stratum_eq_classValue A Fsep N hloop,
    separatingMarkedLeft.map_stratum_eq_classValue A Fsep N hleft,
    separatingMarkedRight.map_stratum_eq_classValue A Fsep N hright]
  abel

end AxiomaticGW.GKM.HodgeDegreeOneRealization
