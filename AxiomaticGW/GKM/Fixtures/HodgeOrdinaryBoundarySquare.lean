/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeGenusTwoPicard
public import AxiomaticGW.GKM.Fixtures.HodgeFullSquare
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroStrataSpecialization

/-!
# A boundary-square realization of the ordinary genus-two unit packet

The genus-two Picard row replaces the one-marked degree-one expression by
the discriminant boundary. The positive-codimension packet specialization
and the loop, mixed and separating excess calculations then express the
realized ordinary class as the square of two actual gluing pushforwards.
-/

@[expose] public section
namespace AxiomaticGW.GKM.HodgeOrdinaryBoundarySquare
open AdmcyclesHodgeStrataCandidates HodgeGenusTwoPicard HodgeDegreeZeroStrataSpecialization

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Realize the unique specialized cycle using the original Picard row and the
primitive geometric inputs for the complete twenty-eight-term square. -/
theorem map_ordinary (X : SurfaceTarget)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fforget : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (Qsquare : ForgetfulSquareCompatibility Fforget F)
    (Qloop : ForgetfulNonseparatingComposition Fforget N)
    (Qsep : ForgetfulSeparatingComposition Fforget F)
    (Hforget : GluingForgetfulCompatibility F N)
    (hTail : PsiBoundaryExpansion.TailCompatible K F N)
    (hTailForget : PsiBoundaryExpansion.TailForgetCompatible C)
    (hLoopGysin : LoopSquareGysin.SelfGysinCompatible F N P)
    (hMixedGysin : LoopSeparatingGysin.MixedGysinCompatible N)
    (hSepGysin : SeparatingSquareGysin.SelfGysinCompatible F P)
    (hbasePsi : (A 2 (Fin 1)).LegPsiCompatible P HodgeDegreeOneRealization.stable)
    (hbaseFund : (A 2 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) HodgeDegreeOneRealization.stable)) = 1)
    (hcorolla : (A 2 (Fin 1)).CorollaForgetfulCompatible
      (A 2 (Option (Fin 1))) Fforget HodgeDegreeOneRealization.stable)
    (hκUp : (A 2 (Option (Fin 1))).KappaForgetfulCompatible
      (A 2 (Option (Option (Fin 1)))) Fforget HodgeDegreeOneRealization.stable.option 1)
    (hpsiUp : (A 2 (Option (Fin 1))).LegPsiCompatible P
      HodgeDegreeOneRealization.stable.option)
    (hpsiUpUp : (A 2 (Option (Option (Fin 1)))).LegPsiCompatible P
      HodgeDegreeOneRealization.stable.option.option)
    (hfundUp : (A 2 (Option (Fin 1))).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Option (Fin 1))
        HodgeDegreeOneRealization.stable.option)) = 1)
    (hfundUpUp : (A 2 (Option (Option (Fin 1)))).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Option (Option (Fin 1)))
        HodgeDegreeOneRealization.stable.option.option)) = 1)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N)
    (hleft : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hright : HodgeDegreeOneRealization.separatingMarkedRight.Compatible A F N)
    (hκLoop : (A 1 (Option (Option (Fin 1)))).KappaForgetfulCompatible
      (A 1 (Option (Option (Option (Fin 1))))) Fforget HodgeKappaLoopProduct.sourceStable 1)
    (hpsiLoopUp : (A 1 (Option (Option (Option (Fin 1))))).LegPsiCompatible P
      HodgeKappaLoopProduct.sourceStable.option)
    (hfundLoopUp : (A 1 (Option (Option (Option (Fin 1))))).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Option (Option (Option (Fin 1))))
        HodgeKappaLoopProduct.sourceStable.option)) = 1)
    (hκM : (A 1 (Option (Fin 1))).KappaForgetfulCompatible
      (A 1 (Option (Option (Fin 1)))) Fforget LoopSeparatingGysin.markedStable 1)
    (hκU : (A 1 (Option (Fin 0))).KappaForgetfulCompatible
      (A 1 (Option (Option (Fin 0)))) Fforget LoopSeparatingGysin.unmarkedStable 1)
    (hpsiMnew : (A 1 (Option (Option (Fin 1)))).LegPsiCompatible P
      LoopSeparatingGysin.markedStable.option)
    (hpsiUnew : (A 1 (Option (Option (Fin 0)))).LegPsiCompatible P
      LoopSeparatingGysin.unmarkedStable.option)
    (hfundUnew : (A 1 (Option (Option (Fin 0)))).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Option (Option (Fin 0)))
        LoopSeparatingGysin.unmarkedStable.option)) = 1)
    (hpsiM : (A 1 (Option (Fin 1))).LegPsiCompatible P LoopSeparatingGysin.markedStable)
    (hpsiU : (A 1 (Option (Fin 0))).LegPsiCompatible P LoopSeparatingGysin.unmarkedStable)
    (hdouble : LoopSquareGluing.doubleLoopExpression.Compatible A F N)
    (hparallel : LoopSquareGluing.parallelFirstExpression.Compatible A F N)
    (hmixedLeft : LoopSeparatingGysin.leftRefinement.Compatible A F N)
    (hmixedRight : LoopSeparatingGysin.rightRefinement.Compatible A F N)
    (hchain : SeparatingSquareGysin.chainExpression.Compatible A F N)
    (hrow : (A 2 (Fin 1)).map (RelationCertificate.interpret columns row) = 0) :
    (A 2 (Fin 1)).map (ordinary X) = ((9 - (X.blowups : ℚ)) / 200) •
      ((1 / 2 : ℚ) • HodgeDegreeOneRealization.loop.classValue F N +
        (2 : ℚ) • HodgeDegreeOneRealization.separatingMarkedLeft.classValue F N) ^ 2 := by
  have hs := HodgeFullSquare.map_raw_0_2_eq_half_square A Fforget F N P K Qsquare Qloop Qsep
    Hforget hTail hTailForget hLoopGysin hMixedGysin hSepGysin hbasePsi hbaseFund hcorolla
    hκUp hpsiUp hpsiUpUp hfundUp hfundUpUp hloop hleft hright hκLoop hpsiLoopUp hfundLoopUp
    hκM hκU hpsiMnew hpsiUnew hfundUnew hpsiM hpsiU hdouble hparallel hmixedLeft hmixedRight
    hchain
  rw [ordinary, map_smul, hs, map_degree_one (A 2 (Fin 1)).map hrow,
    map_boundary A F N hloop hleft, smul_pow, smul_smul, smul_smul]
  congr 1
  ring

end AxiomaticGW.GKM.HodgeOrdinaryBoundarySquare
