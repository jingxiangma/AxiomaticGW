/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.CorollaForgetfulRealization
public import AxiomaticGW.GKM.Fixtures.HodgeKappaSquare

/-!
# Conditional realization of the actual kappa-squared raw corolla

The actual graph is now reached through a universally defined finite operation.
The new hypothesis is compatibility with that operation on all kappa vectors;
no input supplies this raw graph's class or a desired Hodge product. The
geometric validity of the universal operation compatibility remains explicit.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeKappaCorolla

open AdmcyclesHodgeStrataCandidates

/-- The constructed pushforward contains the actual raw21 plus kappa two,
with coefficient one on each term. -/
theorem actual_two_term_push :
    CorollaForgetful.push 2 (Fin 1) HodgeDegreeOneRealization.stable
      (Finsupp.single 1 1) 1 =
      StrataModule.basis rawGraph21 + StrataModule.basis
        (TautologicalStratum.kappaGenerator 2 (Fin 1) HodgeDegreeOneRealization.stable 2) := by
  rw [CorollaForgetful.push_single, HodgeKappaSquare.rawGraph21_eq_kappa_one_squared_corolla,
    ← Finsupp.single_add]
  rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The former raw21 gap is closed conditionally by the universal finite
forgetful-operation law, rather than a graph-specific supplied value. -/
theorem map_rawGraph21_eq_kappa_one_square
    (A : StrataRealization C 2 (Fin 1))
    (B : StrataRealization C 2 (Option (Fin 1)))
    (D : StrataRealization C 2 (Option (Option (Fin 1))))
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Q : ForgetfulSquareCompatibility Fforget F)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C)
    (hc : A.CorollaForgetfulCompatible B Fforget HodgeDegreeOneRealization.stable)
    (hκ : B.KappaForgetfulCompatible D Fforget HodgeDegreeOneRealization.stable.option 1)
    (hpsiB : B.LegPsiCompatible P HodgeDegreeOneRealization.stable.option)
    (hpsiD : D.LegPsiCompatible P HodgeDegreeOneRealization.stable.option.option)
    (hfundB : B.map (StrataModule.basis (TautologicalStratum.fundamental 2
      (Option (Fin 1)) HodgeDegreeOneRealization.stable.option)) = 1)
    (hfundD : D.map (StrataModule.basis (TautologicalStratum.fundamental 2
      (Option (Option (Fin 1))) HodgeDegreeOneRealization.stable.option.option)) = 1) :
    A.map (StrataModule.basis rawGraph21) =
      P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 ^ 2 := by
  have he := A.map_two_kappa_corolla B D Fforget F N P K Q hK H
    HodgeDegreeOneRealization.stable 1 1 hc hκ hpsiB hpsiD hfundB hfundD
  rw [← Finsupp.single_add] at he
  rw [HodgeKappaSquare.rawGraph21_eq_kappa_one_squared_corolla, pow_two]
  exact he

end AxiomaticGW.GKM.HodgeKappaCorolla
