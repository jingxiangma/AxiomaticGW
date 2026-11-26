/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeBoundarySquareCertificate
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroStrataSpecialization

/-!
# Realizing the ordinary degree-two packet by the original PPZ rows

The comparison uses only the three boundary-product Gysin laws, their named
node-psi, fundamental-class and graph-realization inputs, and vanishing of
the original degree-two rows. The auxiliary kappa-two column cancels inside
the row certificate.
-/

@[expose] public section
namespace AxiomaticGW.GKM.HodgeBoundarySquareRealization
open AdmcyclesHodgeStrataCandidates HodgeBoundarySquareRows HodgeBoundarySquareCertificate
open HodgeDegreeZeroStrataSpecialization

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

private theorem square_weights (l s : C.H 2 (Fin 1)) :
    (144 : ℚ) • ((1 / 24 : ℚ) • l) ^ 2 +
      (288 : ℚ) • ((1 / 144 : ℚ) • (l * s)) +
      (576 : ℚ) • ((1 / 144 : ℚ) • s ^ 2) = ((1 / 2 : ℚ) • l + (2 : ℚ) • s) ^ 2 := by
  simp only [pow_two, add_mul, mul_add, smul_mul_smul_comm, smul_smul]
  rw [mul_comm s l]
  module

/-- The ordinary genus-two unit packet is the stated multiple of the geometric
discriminant boundary square under the original degree-two row and Gysin inputs. -/
theorem map_ordinary (X : SurfaceTarget)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hLoopGysin : LoopSquareGysin.SelfGysinCompatible F N P)
    (hMixedGysin : LoopSeparatingGysin.MixedGysinCompatible N)
    (hSepGysin : SeparatingSquareGysin.SelfGysinCompatible F P)
    (hglue : (A 1 LoopSquareGysin.SourceLabels).NonseparatingCompatible
      (A 2 (Fin 1)) N HodgeDegreeOneRealization.stable)
    (hpsi : (A 1 LoopSquareGysin.SourceLabels).LegPsiCompatible P LoopSquareGysin.sourceStable)
    (hfund : (A 1 LoopSquareGysin.SourceLabels).map (StrataModule.basis HodgeNodeNormal.source) = 1)
    (hpsiM : (A 1 (Option (Fin 1))).LegPsiCompatible P LoopSeparatingGysin.markedStable)
    (hpsiU : (A 1 (Option (Fin 0))).LegPsiCompatible P LoopSeparatingGysin.unmarkedStable)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hdouble : LoopSquareGluing.doubleLoopExpression.Compatible A F N)
    (hparallel : LoopSquareGluing.parallelFirstExpression.Compatible A F N)
    (hleft : LoopSeparatingGysin.leftRefinement.Compatible A F N)
    (hright : LoopSeparatingGysin.rightRefinement.Compatible A F N)
    (hchain : SeparatingSquareGysin.chainExpression.Compatible A F N)
    (hrows : ∀ i, witness.weights i ≠ 0 →
      (A 2 (Fin 1)).map (RelationCertificate.interpret columns (rows i)) = 0) :
    (A 2 (Fin 1)).map (ordinary X) = ((9 - (X.blowups : ℚ)) / 200) •
      ((1 / 2 : ℚ) • HodgeDegreeOneRealization.loop.classValue F N +
        (2 : ℚ) • HodgeDegreeOneRealization.separatingMarkedLeft.classValue F N) ^ 2 := by
  have hl := HodgeLoopSquare.map_packetPart_eq_actual_loop_square A F N P hLoopGysin hglue hpsi
    hfund hdouble hparallel hloop
  have hm := HodgeLoopSeparatingProduct.map_packetPart_eq_raw_product A F N hMixedGysin hloop hsep
    hleft hright
  have hs := HodgeSeparatingSquare.map_packetPart_eq_raw_square A F N P hSepGysin hsep hpsiM
    hpsiU hchain
  change (A 2 (Fin 1)).map LoopSquarePacketBinding.packetPart =
    ((1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph3)) ^ 2 at hl
  rw [ordinary, map_smul, map_half _ hrows, squarePacket, map_add, map_add, map_smul, map_smul,
    map_smul, hl, hm, hs, square_weights, HodgeDegreeOneRealization.rawGraph3_eq_loop,
    HodgeDegreeOneRealization.rawGraph4_eq_left,
    HodgeDegreeOneRealization.loop.map_stratum_eq_classValue A F N hloop,
    HodgeDegreeOneRealization.separatingMarkedLeft.map_stratum_eq_classValue A F N hsep, smul_smul]
  congr 1
  ring

end AxiomaticGW.GKM.HodgeBoundarySquareRealization
