/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.ForgetfulKappa
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeOneRealization

/-!
# The actual kappa-squared corolla and the square of its degree-one source

The degree-two raw graph is bound to its actual decoration, with two factors
of kappa one. Independently, generator realization and the universal forgetful
map laws identify the square of the realized degree-one kappa source with a
corrected pushforward. No equality between these two constructions is claimed:
an arbitrary linear strata realization need not preserve kappa products.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeKappaSquare

open AdmcyclesHodgeStrataCandidates

/-- The actual corolla carries kappa one twice, rather than kappa two once. -/
theorem rawGraph21_eq_kappa_one_squared_corolla :
    rawGraph21 = TautologicalStratum.oneVertex 2 (Fin 1)
      HodgeDegreeOneRealization.stable (Finsupp.single 1 2) (fun _ ↦ 0) := by
  have hvector :
      DecoratedStableGraph.kappaVector 4 (![2, 0, 0, 0] : Fin 4 → ℕ) =
        (Finsupp.single 1 2 : ℕ+ →₀ ℕ) := by
    have hcoordinates :
        (fun i : Fin 4 ↦ (Finsupp.single 1 2 : ℕ+ →₀ ℕ)
          (DecoratedStableGraph.kappaIndex 4 i)) = ![2, 0, 0, 0] := by
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
  rw [← hvector]
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Square the realized actual degree-one kappa source using universal map
laws. This does not assert a value for the realization of `rawGraph21`. -/
theorem square_map_rawGraph2_eq_corrected_push
    (A : StrataRealization C 2 (Fin 1))
    (B : StrataRealization C 2 (Option (Fin 1)))
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Q : ForgetfulSquareCompatibility Fforget F)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (hκ : A.KappaForgetfulCompatible B Fforget HodgeDegreeOneRealization.stable 1)
    (hpsi : B.LegPsiCompatible P HodgeDegreeOneRealization.stable.option)
    (hfund : B.map (StrataModule.basis (TautologicalStratum.fundamental 2
      (Option (Fin 1)) HodgeDegreeOneRealization.stable.option)) = 1) :
    A.map (StrataModule.basis rawGraph2) ^ 2 =
      Fforget.push 2 (Fin 1) HodgeDegreeOneRealization.stable
        (P.kappa Fforget 2 (Option (Fin 1)) HodgeDegreeOneRealization.stable.option 1 *
          P.psi 2 (Option (Fin 1)) HodgeDegreeOneRealization.stable.option none ^ 2) -
        P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 2 := by
  rw [HodgeDegreeOneRealization.rawGraph2_eq_kappa,
    A.map_kappaGenerator B Fforget P HodgeDegreeOneRealization.stable 1 hκ hpsi hfund]
  exact Q.kappa_one_square N P K hK H 2 (Fin 1) HodgeDegreeOneRealization.stable

end AxiomaticGW.GKM.HodgeKappaSquare
