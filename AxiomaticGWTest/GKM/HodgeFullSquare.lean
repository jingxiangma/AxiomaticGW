/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeFullSquare

/-! All three held surface assemblies consume the actual half-square theorem.
The signed raw fundamental terms are retained explicitly. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.HodgeFullSquare

open AxiomaticGW AxiomaticGW.GKM AdmcyclesHodgeStrataCandidates EquivariantCoefficients

variable {C : StableCurveCohomology Coefficient} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- These are the complete actual incoming surface assemblies, without replacing the raw unit. -/
theorem three_target_assemblies
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
    (hchain : SeparatingSquareGysin.chainExpression.Compatible A F N) :
    HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass (A 2 (Fin 1)) =
      (x ^ 2 - x * y + y ^ 2) • (A 2 (Fin 1)).map raw00Degree0 +
        (9 / 2 : Coefficient) • ((A 2 (Fin 1)).map raw01Degree1) ^ 2 ∧
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass (A 2 (Fin 1)) =
      (4 : Coefficient) • ((A 2 (Fin 1)).map raw01Degree1) ^ 2 ∧
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass (A 2 (Fin 1)) =
      (-(x ^ 2 - x * y + y ^ 2)) • (A 2 (Fin 1)).map raw00Degree0 +
        (7 / 2 : Coefficient) • ((A 2 (Fin 1)).map raw01Degree1) ^ 2 := by
  have hh := HodgeFullSquare.map_raw_0_2_eq_half_square A Fforget F N P K Qsquare Qloop Qsep Hforget hTail hTailForget
    hLoopGysin hMixedGysin hSepGysin hbasePsi hbaseFund hcorolla hκUp hpsiUp hpsiUpUp
    hfundUp hfundUpUp hloop hleft hright hκLoop hpsiLoopUp hfundLoopUp hκM hκU
    hpsiMnew hpsiUnew hfundUnew hpsiM hpsiU hdouble hparallel hmixedLeft hmixedRight hchain
  change (A 2 (Fin 1)).map raw02Degree2 =
    (algebraMap ℚ Coefficient (1 / 2 : ℚ)) • ((A 2 (Fin 1)).map raw01Degree1) ^ 2 at hh
  norm_num only [map_div₀, map_one, map_ofNat] at hh
  have h9 : (9 : Coefficient) * (1 / 2) = 9 / 2 := by ring
  have h8 : (8 : Coefficient) * (1 / 2) = 4 := by
    have hq := congrArg (algebraMap ℚ Coefficient) (show (8 : ℚ) * (1 / 2) = 4 by norm_num)
    simpa only [map_mul, map_div₀, map_one, map_ofNat] using hq
  have h7 : (7 : Coefficient) * (1 / 2) = 7 / 2 := by ring
  constructor
  · rw [HodgeDegreeTwoRawRelation.plane_candidateClass_eq_raw_degree_two, hh, smul_smul, h9]
  constructor
  · rw [HodgeDegreeTwoRawRelation.oneBlowup_candidateClass_eq_raw_degree_two, hh, smul_smul, h8]
  · rw [HodgeDegreeTwoRawRelation.twoBlowups_candidateClass_eq_raw_degree_two, hh, smul_smul, h7]

end AxiomaticGWTest.GKM.HodgeFullSquare
