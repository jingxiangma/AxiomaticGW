/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareGysin

/-!
# Conditional geometric image of the five held loop-square occurrences

The exact existing packet binding and primitive gluing/psi realization laws
are combined with the explicit arbitrary-class Gysin obligation. No boundary
square is an input, and that new geometric obligation is not instantiated.
The other packet positions and the Hodge/GRR identification remain separate.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeLoopSquare

open LoopSquareGluing LoopSquareGysin AdmcyclesHodgeStrataCandidates

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The double-loop class is the same proper composition used by the Gysin operator. -/
theorem doubleLoop_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    doubleLoopExpression.classValue F N = outerPush N (doublePush N 1) := rfl

/-- The first parallel source has exactly the existing ordered component units. -/
theorem parallel_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    parallelFirstExpression.classValue F N = outerPush N (parallelPush F 0 1) := rfl

/-- The actual degree-one loop uses the same raw ordered gluing convention. -/
theorem loop_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    HodgeDegreeOneRealization.loop.classValue F N = outerPush N 1 := rfl

/-- Conditional image of exactly positions 3,4,18,21,23, retaining the input weight. -/
theorem map_packetPart_eq_weighted_square
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (H : SelfGysinCompatible F N P)
    (hglue : (A 1 SourceLabels).NonseparatingCompatible
      (A 2 (Fin 1)) N HodgeDegreeOneRealization.stable)
    (hpsi : (A 1 SourceLabels).LegPsiCompatible P sourceStable)
    (hfund : (A 1 SourceLabels).map (StrataModule.basis HodgeNodeNormal.source) = 1)
    (hdouble : doubleLoopExpression.Compatible A F N)
    (hparallel : parallelFirstExpression.Compatible A F N) :
    (A 2 (Fin 1)).map LoopSquarePacketBinding.packetPart =
      ((1 / 24 : ℚ) • outerPush N 1) ^ 2 := by
  rw [LoopSquareGluing.map_packetPart A F N P hglue hpsi hfund hdouble hparallel,
    doubleLoop_operator_value, parallel_operator_value]
  change (1 / 24 : ℚ) ^ 2 •
    ((2 : ℚ) • outerPush N (normalClass P) + outerPush N (doublePush N 1) +
      (4 : ℚ) • outerPush N (parallelPush F 0 1)) = _
  calc
    _ = (1 / 24 : ℚ) ^ 2 • outerPush N 1 ^ 2 := by
      congr 1
      rw [raw_loop_square F N P H]
      module
    _ = ((1 / 24 : ℚ) • outerPush N 1) ^ 2 := (smul_pow _ _ _).symm

/-- Bind the exact original source column and coefficient, without Hodge identification. -/
theorem map_packetPart_eq_actual_loop_square
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (H : SelfGysinCompatible F N P)
    (hglue : (A 1 SourceLabels).NonseparatingCompatible
      (A 2 (Fin 1)) N HodgeDegreeOneRealization.stable)
    (hpsi : (A 1 SourceLabels).LegPsiCompatible P sourceStable)
    (hfund : (A 1 SourceLabels).map (StrataModule.basis HodgeNodeNormal.source) = 1)
    (hdouble : doubleLoopExpression.Compatible A F N)
    (hparallel : parallelFirstExpression.Compatible A F N)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N) :
    (A 2 (Fin 1)).map LoopSquarePacketBinding.packetPart =
      (raw01Degree1Coordinates 2 •
        (A 2 (Fin 1)).map (StrataModule.basis (raw01Degree1Columns 2))) ^ 2 := by
  change (A 2 (Fin 1)).map LoopSquarePacketBinding.packetPart =
    ((1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph3)) ^ 2
  rw [HodgeDegreeOneRealization.rawGraph3_eq_loop,
    HodgeDegreeOneRealization.loop.map_stratum_eq_classValue A F N hloop,
    loop_operator_value]
  exact map_packetPart_eq_weighted_square A F N P H hglue hpsi hfund hdouble hparallel

end AxiomaticGW.GKM.HodgeLoopSquare
