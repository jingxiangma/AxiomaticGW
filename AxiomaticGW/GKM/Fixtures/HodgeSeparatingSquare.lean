/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SeparatingSquareGysin
public import AxiomaticGW.GKM.Fixtures.HodgeLoopSeparatingProduct

/-!
# Conditional separating square in the six remaining packet occurrences

The normal term is constructed using the existing distinguished-leg psi and
separating operations. The disjoint refinement is an independent two-gluing
expression. Actual graph isomorphisms and original coefficients are retained.
The product conclusion is conditional on the all-source Gysin input; no
geometric Hodge identification or instantiated excess model is asserted.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeSeparatingSquare

open LoopSeparatingGysin SeparatingSquareGysin AdmcyclesHodgeStrataCandidates
open HodgeDegreeTwoRawRelation
open scoped TensorProduct

noncomputable def markedUnit : TautologicalStratum 1 MarkedLabels :=
  TautologicalStratum.fundamental 1 MarkedLabels markedStable

noncomputable def unmarkedUnit : TautologicalStratum 1 UnmarkedLabels :=
  TautologicalStratum.fundamental 1 UnmarkedLabels unmarkedStable

/-- Decorate the marked component's node before raw separating gluing. -/
theorem rawGraph10_eq_marked_node :
    rawGraph10 = ((markedUnit.addLegPsi (Pi.single none 1)).separating unmarkedUnit).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1) := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Decorate the other ordered node branch independently. -/
theorem rawGraph11_eq_unmarked_node :
    rawGraph11 = (markedUnit.separating (unmarkedUnit.addLegPsi (Pi.single none 1))).relabel
      (finSumFinEquiv : Fin 1 ⊕ Fin 0 ≃ Fin 1) := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Construct the rational middle with its two elliptic tails by two gluings. -/
theorem rawGraph16_eq_chain : rawGraph16 = chainExpression.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- All six incoming positions, including both equal chain occurrences. -/
noncomputable def packetPart : StrataModule 2 (Fin 1) :=
  raw11Degree2Coordinates 5 • StrataModule.basis (raw11Degree2Columns 5) +
  raw11Degree2Coordinates 6 • StrataModule.basis (raw11Degree2Columns 6) +
  raw11Degree2Coordinates 7 • StrataModule.basis (raw11Degree2Columns 7) +
  raw11Degree2Coordinates 8 • StrataModule.basis (raw11Degree2Columns 8) +
  raw11Degree2Coordinates 19 • StrataModule.basis (raw11Degree2Columns 19) +
  raw11Degree2Coordinates 20 • StrataModule.basis (raw11Degree2Columns 20)

theorem packetPart_eq_raw_sum :
    packetPart = (1 / 144 : ℚ) •
      (-StrataModule.basis rawGraph10 - StrataModule.basis rawGraph11 +
        StrataModule.basis rawGraph16) := by
  change
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph24 +
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph25 +
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph10 +
    (-1 / 288 : ℚ) • StrataModule.basis rawGraph11 +
    (1 / 288 : ℚ) • StrataModule.basis rawGraph29 +
    (1 / 288 : ℚ) • StrataModule.basis rawGraph30 = _
  rw [rawGraphIso5, rawGraphIso6, rawGraphIso19, rawGraphIso20]
  module

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The disjoint chain uses exactly the first contraction followed by the outer map. -/
theorem chain_operator_value (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    chainExpression.classValue F N = separatingPush F (refinementPush F 1) := rfl

/-- Existing primitive realization laws give the signed cotangent normal expression. -/
theorem map_node_sum
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hpsiM : (A 1 MarkedLabels).LegPsiCompatible P markedStable)
    (hpsiU : (A 1 UnmarkedLabels).LegPsiCompatible P unmarkedStable) :
    -(A 2 (Fin 1)).map (StrataModule.basis rawGraph10) -
      (A 2 (Fin 1)).map (StrataModule.basis rawGraph11) =
        separatingPush F (normalClass P) := by
  have hM : (A 1 MarkedLabels).map (StrataModule.basis markedUnit) = 1 := hsep.1.1
  have hU : (A 1 UnmarkedLabels).map (StrataModule.basis unmarkedUnit) = 1 := hsep.1.2.1
  have hm : (A 2 (Fin 1)).map (StrataModule.basis rawGraph10) =
      separatingPush F (P.psi 1 MarkedLabels markedStable none ⊗ₜ[R] 1) := by
    rw [rawGraph10_eq_marked_node, hsep.2, hsep.1.2.2,
      (A 1 MarkedLabels).map_addLegPsi_one P markedStable hpsiM,
      hM, hU, one_mul]
    rfl
  have hu : (A 2 (Fin 1)).map (StrataModule.basis rawGraph11) =
      separatingPush F (1 ⊗ₜ[R] P.psi 1 UnmarkedLabels unmarkedStable none) := by
    rw [rawGraph11_eq_unmarked_node, hsep.2, hsep.1.2.2,
      (A 1 UnmarkedLabels).map_addLegPsi_one P unmarkedStable hpsiU,
      hM, hU, one_mul]
    rfl
  rw [hm, hu, normalClass, map_neg, map_add]
  abel

/-- Exact six-slot image as the square of the raw marked separating class. -/
theorem map_packetPart_eq_raw_square
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F P)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hpsiM : (A 1 MarkedLabels).LegPsiCompatible P markedStable)
    (hpsiU : (A 1 UnmarkedLabels).LegPsiCompatible P unmarkedStable)
    (hchain : chainExpression.Compatible A F N) :
    (A 2 (Fin 1)).map packetPart = (1 / 144 : ℚ) •
      (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) ^ 2 := by
  rw [packetPart_eq_raw_sum, map_smul, map_add, map_sub, map_neg,
    map_node_sum A F N P hsep hpsiM hpsiU,
    rawGraph16_eq_chain, chainExpression.map_stratum_eq_classValue A F N hchain,
    chain_operator_value, HodgeDegreeOneRealization.rawGraph4_eq_left,
    HodgeDegreeOneRealization.separatingMarkedLeft.map_stratum_eq_classValue A F N hsep,
    HodgeLoopSeparatingProduct.separating_operator_value,
    raw_separating_square F P H]

/-- Keep both original ordered separating columns and their exact weights. -/
theorem map_packetPart_eq_actual_separating_square
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (H : SelfGysinCompatible F P)
    (hsep : HodgeDegreeOneRealization.separatingMarkedLeft.Compatible A F N)
    (hpsiM : (A 1 MarkedLabels).LegPsiCompatible P markedStable)
    (hpsiU : (A 1 UnmarkedLabels).LegPsiCompatible P unmarkedStable)
    (hchain : chainExpression.Compatible A F N) :
    (A 2 (Fin 1)).map packetPart =
      ((raw01Degree1Coordinates 3 •
        (A 2 (Fin 1)).map (StrataModule.basis (raw01Degree1Columns 3))) +
       (raw01Degree1Coordinates 4 •
        (A 2 (Fin 1)).map (StrataModule.basis (raw01Degree1Columns 4)))) ^ 2 := by
  rw [map_packetPart_eq_raw_square A F N P H hsep hpsiM hpsiU hchain]
  change (1 / 144 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) ^ 2 =
    ((1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph4) +
      (1 / 24 : ℚ) • (A 2 (Fin 1)).map (StrataModule.basis rawGraph5)) ^ 2
  rw [HodgeLoopSeparatingProduct.rawGraph5_eq_rawGraph4, ← add_smul, smul_pow]
  norm_num

end AxiomaticGW.GKM.HodgeSeparatingSquare
