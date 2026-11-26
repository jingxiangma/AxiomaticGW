/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeExternalPsi
public import AxiomaticGW.GKM.Fixtures.HodgeKappaLoopProduct
public import AxiomaticGW.GKM.Fixtures.HodgeKappaSeparatingProduct
public import AxiomaticGW.GKM.Fixtures.HodgeKappaCorolla
public import AxiomaticGW.GKM.Fixtures.HodgeLoopSquare
public import AxiomaticGW.GKM.Fixtures.HodgeSeparatingSquare

/-!
# The complete actual degree-two packet as a conditional square

Every one of the original 28 occurrences is retained in a checked partition.
The already derived external-psi, kappa, loop, mixed, and separating products
are then assembled. No new geometric law is introduced by this aggregation.
All primitive compatibility and fundamental-class normalization inputs remain
explicit. The raw relation yields the second packet as half this square;
neither packet is identified with a geometric Hodge class by this result.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeFullSquare

open AdmcyclesHodgeStrataCandidates
open scoped BigOperators

/-- Original positions grouped as psi, kappa, loop, mixed, separating. -/
def pieceOrder : Fin 28 → Fin 28 :=
  ![0, 1, 2, 9, 15, 10, 11, 12, 13, 14, 16, 3, 4, 18, 21, 23,
    17, 22, 24, 25, 26, 27, 5, 6, 7, 8, 19, 20]

/-- Occurrence completeness is independent of equal graph columns or coefficients. -/
theorem pieceOrder_bijective : Function.Bijective pieceOrder := by
  decide +kernel

/-- Six original kappa positions, including both two-component separating sums. -/
noncomputable def packetKappaPart : StrataModule 2 (Fin 1) :=
  raw_1_1_degree2Coordinates 10 • StrataModule.basis (raw_1_1_degree2Columns 10) +
  raw_1_1_degree2Coordinates 11 • StrataModule.basis (raw_1_1_degree2Columns 11) +
  raw_1_1_degree2Coordinates 12 • StrataModule.basis (raw_1_1_degree2Columns 12) +
  raw_1_1_degree2Coordinates 13 • StrataModule.basis (raw_1_1_degree2Columns 13) +
  raw_1_1_degree2Coordinates 14 • StrataModule.basis (raw_1_1_degree2Columns 14) +
  raw_1_1_degree2Coordinates 16 • StrataModule.basis (raw_1_1_degree2Columns 16)

theorem packetKappaPart_eq_raw_sum :
    packetKappaPart = (1 / 144 : ℚ) •
      (StrataModule.basis rawGraph17 +
        (StrataModule.basis rawGraph13 + StrataModule.basis rawGraph26) +
        (StrataModule.basis rawGraph14 + StrataModule.basis rawGraph27) +
        StrataModule.basis rawGraph21) := by
  change
    (1 / 144 : ℚ) • StrataModule.basis rawGraph17 +
    (1 / 144 : ℚ) • StrataModule.basis rawGraph26 +
    (1 / 144 : ℚ) • StrataModule.basis rawGraph27 +
    (1 / 144 : ℚ) • StrataModule.basis rawGraph13 +
    (1 / 144 : ℚ) • StrataModule.basis rawGraph14 +
    (1 / 144 : ℚ) • StrataModule.basis rawGraph21 = _
  module

set_option maxRecDepth 4000 in
/-- This is an equality of the complete incoming expression before realization. -/
theorem original_packet_partition :
    raw_1_1_degree2 = HodgeExternalPsi.packetPsiPart + packetKappaPart +
      LoopSquarePacketBinding.packetPart + HodgeLoopSeparatingProduct.packetPart +
        HodgeSeparatingSquare.packetPart := by
  let f : Fin 28 → StrataModule 2 (Fin 1) := fun i ↦
    raw_1_1_degree2Coordinates i • StrataModule.basis (raw_1_1_degree2Columns i)
  change (∑ i : Fin 28, f i) =
    (f 0 + f 1 + f 2 + f 9 + f 15) +
    (f 10 + f 11 + f 12 + f 13 + f 14 + f 16) +
    (f 3 + f 4 + f 18 + f 21 + f 23) +
    (f 17 + f 22 + f 24 + f 25 + f 26 + f 27) +
    (f 5 + f 6 + f 7 + f 8 + f 19 + f 20)
  rw [← pieceOrder_bijective.sum_comp f]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 9 + (f 15 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (
    f 16 + (f 3 + (f 4 + (f 18 + (f 21 + (f 23 + (f 17 + (f 22 + (f 24 + (f 25 + (
    f 26 + (f 27 + (f 5 + (f 6 + (f 7 + (f 8 + (f 19 + (f 20))))))))))))))))))))))))))) = _
  simp only [add_assoc]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The final polynomial step keeps all five degree-one contributions distinct. -/
theorem five_term_algebra (p k l d e : C.H 2 (Fin 1)) :
    (1 / 144 : ℚ) • p ^ 2 +
    (-1 / 6 : ℚ) • (((1 / 12 : ℚ) • k + (1 / 24 : ℚ) • l +
      (1 / 24 : ℚ) • d + (1 / 24 : ℚ) • e) * p) +
    (1 / 144 : ℚ) • (k * l + k * d + k * e + k ^ 2) +
    ((1 / 24 : ℚ) • l) ^ 2 +
    (2 : ℚ) • (((1 / 24 : ℚ) • l) *
      ((1 / 24 : ℚ) • d + (1 / 24 : ℚ) • e)) +
    ((1 / 24 : ℚ) • d + (1 / 24 : ℚ) • e) ^ 2 =
    ((-1 / 12 : ℚ) • p + (1 / 12 : ℚ) • k + (1 / 24 : ℚ) • l +
      (1 / 24 : ℚ) • d + (1 / 24 : ℚ) • e) ^ 2 := by
  simp only [pow_two, add_mul, mul_add, smul_add, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  simp only [mul_comm]
  module

/-- Assemble every actual occurrence using the previously named primitive inputs. -/
theorem map_raw_1_1_eq_square
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
    (A 2 (Fin 1)).map raw_1_1_degree2 = ((A 2 (Fin 1)).map raw_0_1_degree1) ^ 2 := by
  have hp : (A 2 (Fin 1)).map (StrataModule.basis rawGraph1) =
      P.psi 2 (Fin 1) HodgeDegreeOneRealization.stable 0 := by
    rw [HodgeDegreeOneRealization.rawGraph1_eq_psi,
      (A 2 (Fin 1)).map_addLegPsi P HodgeDegreeOneRealization.stable hbasePsi,
      hbaseFund, one_mul]
    simp only [PsiClasses.monomial, Fin.prod_univ_one, pow_one]
  have hk : (A 2 (Fin 1)).map (StrataModule.basis rawGraph2) =
      P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 := by
    rw [HodgeDegreeOneRealization.rawGraph2_eq_kappa]
    exact (A 2 (Fin 1)).map_kappaGenerator (A 2 (Option (Fin 1))) Fforget P
      HodgeDegreeOneRealization.stable 1 (hcorolla.kappaGenerator 1) hpsiUp hfundUp
  have hsource : (A 2 (Fin 1)).map raw_0_1_degree1 =
      (-1 / 12 : ℚ) • P.psi 2 (Fin 1) HodgeDegreeOneRealization.stable 0 +
      (1 / 12 : ℚ) • P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph3) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph5) := by
    simp only [raw_0_1_degree1, RelationCertificate.interpret_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, raw_0_1_degree1Columns, raw_0_1_degree1Coordinates,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      map_add, map_smul, add_zero, hp, hk]
    abel
  have hnonPsi : (A 2 (Fin 1)).map HodgeExternalPsi.nonPsiSource =
      (1 / 12 : ℚ) • P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph3) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph5) := by
    simp only [HodgeExternalPsi.nonPsiSource, map_add, map_smul]
    change (1 / 12 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph2) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph3) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph5) = _
    rw [hk]
  have hkl := HodgeKappaLoopProduct.map_rawGraph17_eq_kappa_mul_loop
    A Fforget F N P Qloop Hforget hloop hκLoop hpsiLoopUp hfundLoopUp
  have hkd := HodgeKappaSeparatingProduct.map_left_pair_eq_kappa_mul_boundary
    A Fforget F N P Qsep Hforget hκM hκU hpsiMnew hpsiUnew hloop.1 hfundUnew hleft
  have hke := HodgeKappaSeparatingProduct.map_right_pair_eq_kappa_mul_boundary
    A Fforget F N P Qsep Hforget hκM hκU hpsiMnew hpsiUnew hloop.1 hfundUnew hright
  have hkk := HodgeKappaCorolla.map_rawGraph21_eq_kappa_one_square
    (A 2 (Fin 1)) (A 2 (Option (Fin 1))) (A 2 (Option (Option (Fin 1))))
    Fforget F N P K Qsquare hTail hTailForget hcorolla hκUp hpsiUp hpsiUpUp hfundUp hfundUpUp
  have hkappaPart : (A 2 (Fin 1)).map packetKappaPart = (1 / 144 : ℚ) •
      (P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
          (A 2 (Fin 1)).map (StrataModule.basis rawGraph3) +
        P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
          (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) +
        P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 *
          (A 2 (Fin 1)).map (StrataModule.basis rawGraph5) +
        P.kappa Fforget 2 (Fin 1) HodgeDegreeOneRealization.stable 1 ^ 2) := by
    rw [packetKappaPart_eq_raw_sum]
    simp only [map_smul, map_add]
    rw [hkl, hkd, hke, hkk]
  have hl := HodgeLoopSquare.map_packetPart_eq_actual_loop_square
    A F N P hLoopGysin hloop.2 hpsiMnew hloop.1 hdouble hparallel hloop
  have hm := HodgeLoopSeparatingProduct.map_packetPart_eq_actual_mixed_product
    A F N hMixedGysin hloop hleft hmixedLeft hmixedRight
  have hd := HodgeSeparatingSquare.map_packetPart_eq_actual_separating_square
    A F N P hSepGysin hleft hpsiM hpsiU hchain
  rw [original_packet_partition]
  simp only [map_add]
  rw [HodgeExternalPsi.map_packetPsiPart_normalized (A 2 (Fin 1)) P hbasePsi hbaseFund,
    hnonPsi, hkappaPart, hl, hm, hd, hsource]
  exact five_term_algebra _ _ _ _ _

/-- The already checked raw relation yields the second full packet as half the square. -/
theorem map_raw_0_2_eq_half_square
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
    (A 2 (Fin 1)).map raw_0_2_degree2 =
      (1 / 2 : ℚ) • ((A 2 (Fin 1)).map raw_0_1_degree1) ^ 2 := by
  have hs := map_raw_1_1_eq_square A Fforget F N P K Qsquare Qloop Qsep Hforget hTail hTailForget
    hLoopGysin hMixedGysin hSepGysin hbasePsi hbaseFund hcorolla hκUp hpsiUp hpsiUpUp
    hfundUp hfundUpUp hloop hleft hright hκLoop hpsiLoopUp hfundLoopUp hκM hκU
    hpsiMnew hpsiUnew hfundUnew hpsiM hpsiU hdouble hparallel hmixedLeft hmixedRight hchain
  rw [HodgeDegreeTwoRawRelation.raw_degree_two_equal, map_smul] at hs
  calc
    _ = (1 / 2 : ℚ) • ((2 : ℚ) • (A 2 (Fin 1)).map raw_0_2_degree2) := by
      rw [smul_smul]
      norm_num only [one_smul]
    _ = _ := congrArg (fun x : C.H 2 (Fin 1) ↦ (1 / 2 : ℚ) • x) hs

end AxiomaticGW.GKM.HodgeFullSquare
