/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSeparatingGysin
public import AxiomaticGW.GKM.Fixtures.HodgeDegreeTwoRawRelation

/-!
# Conditional image of the six loop–separating packet occurrences

All six original indices and coefficients are retained before the existing
raw graph isomorphisms collect them. The two raw gluing expressions are bound
independently to the packet. A new arbitrary-class geometric base-change input
then gives their image as the mixed product of the original degree-one columns.
No geometric realization of that input, Hodge identity, or full product is claimed.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeLoopSeparatingProduct

open LoopSeparatingGysin AdmcyclesHodgeStrataCandidates HodgeDegreeTwoRawRelation
open scoped TensorProduct

/-- The exact marked rational loop comes from the first ordered composition. -/
theorem rawGraph18_eq_leftRefinement : rawGraph18 = leftRefinement.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The exact unmarked rational loop comes from the second ordered composition. -/
theorem rawGraph19_eq_rightRefinement : rawGraph19 = rightRefinement.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Reversing the two ordered separating presentations preserves their raw class. -/
theorem rawGraph5_eq_rawGraph4 : rawGraph5 = rawGraph4 := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Exactly the six incoming occurrences, before quotient collection. -/
noncomputable def packetPart : StrataModule 2 (Fin 1) :=
  raw11Degree2Coordinates 17 • StrataModule.basis (raw11Degree2Columns 17) +
  raw11Degree2Coordinates 22 • StrataModule.basis (raw11Degree2Columns 22) +
  raw11Degree2Coordinates 24 • StrataModule.basis (raw11Degree2Columns 24) +
  raw11Degree2Coordinates 25 • StrataModule.basis (raw11Degree2Columns 25) +
  raw11Degree2Coordinates 26 • StrataModule.basis (raw11Degree2Columns 26) +
  raw11Degree2Coordinates 27 • StrataModule.basis (raw11Degree2Columns 27)

theorem packetPart_eq_raw_sum :
    packetPart = (1 / 144 : ℚ) •
      (StrataModule.basis rawGraph18 + StrataModule.basis rawGraph19) := by
  change
    (1 / 288 : ℚ) • StrataModule.basis rawGraph18 +
    (1 / 288 : ℚ) • StrataModule.basis rawGraph32 +
    (1 / 576 : ℚ) • StrataModule.basis rawGraph33 +
    (1 / 576 : ℚ) • StrataModule.basis rawGraph34 +
    (1 / 576 : ℚ) • StrataModule.basis rawGraph35 +
    (1 / 576 : ℚ) • StrataModule.basis rawGraph36 = _
  rw [rawGraphIso22, rawGraphIso24, rawGraphIso25, rawGraphIso26, rawGraphIso27]
  module

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

theorem leftRefinement_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    leftRefinement.classValue F N =
      separatingPush F (N.push 0 (Option (Fin 1)) markedStable 1 ⊗ₜ[R] 1) := rfl

theorem rightRefinement_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    rightRefinement.classValue F N =
      separatingPush F (1 ⊗ₜ[R] N.push 0 (Option (Fin 0)) unmarkedStable 1) := rfl

theorem loop_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    HodgeDegreeOneRealization.loop.classValue F N = loopPush N 1 := rfl

theorem separating_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    HodgeDegreeOneRealization.separatingMarkedLeft.classValue F N =
      separatingPush F 1 := rfl

/-- The unit product is a consequence of the all-class geometric input. -/
theorem map_packetPart_eq_raw_product
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : MixedGysinCompatible N)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hleft : leftRefinement.Compatible A F N)
    (hright : rightRefinement.Compatible A F N) :
    (A 2 (Fin 1)).map packetPart = (1 / 144 : ℚ) •
      ((A 2 (Fin 1)).map (StrataModule.basis rawGraph3) *
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph4)) := by
  rw [packetPart_eq_raw_sum, map_smul, map_add,
    rawGraph18_eq_leftRefinement, rawGraph19_eq_rightRefinement,
    leftRefinement.map_stratum_eq_classValue A F N hleft,
    rightRefinement.map_stratum_eq_classValue A F N hright,
    leftRefinement_operator_value, rightRefinement_operator_value,
    HodgeDegreeOneRealization.rawGraph3_eq_loop,
    HodgeDegreeOneRealization.rawGraph4_eq_left,
    HodgeDegreeOneRealization.loop.map_stratum_eq_classValue A F N hloop,
    HodgeDegreeOneRealization.separatingMarkedLeft.map_stratum_eq_classValue A F N hsep,
    loop_operator_value, separating_operator_value, unit_product F N H]

/-- Both original ordered separating columns and all original weights remain visible. -/
theorem map_packetPart_eq_actual_mixed_product
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : MixedGysinCompatible N)
    (hloop : HodgeDegreeOneRealization.loop.Compatible A F N)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hleft : leftRefinement.Compatible A F N)
    (hright : rightRefinement.Compatible A F N) :
    (A 2 (Fin 1)).map packetPart = (2 : ℚ) •
      ((raw01Degree1Coordinates 2 •
        (A 2 (Fin 1)).map (StrataModule.basis (raw01Degree1Columns 2))) *
      ((raw01Degree1Coordinates 3 •
        (A 2 (Fin 1)).map (StrataModule.basis (raw01Degree1Columns 3))) +
      (raw01Degree1Coordinates 4 •
        (A 2 (Fin 1)).map (StrataModule.basis (raw01Degree1Columns 4))))) := by
  rw [map_packetPart_eq_raw_product A F N H hloop hsep hleft hright]
  change (1 / 144 : ℚ) •
      ((A 2 (Fin 1)).map (StrataModule.basis rawGraph3) *
        (A 2 (Fin 1)).map (StrataModule.basis rawGraph4)) =
    (2 : ℚ) • (((1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph3)) *
      ((1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) +
        (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph5)))
  rw [rawGraph5_eq_rawGraph4, ← add_smul, smul_mul_smul_comm, smul_smul]
  norm_num

end AxiomaticGW.GKM.HodgeLoopSeparatingProduct
