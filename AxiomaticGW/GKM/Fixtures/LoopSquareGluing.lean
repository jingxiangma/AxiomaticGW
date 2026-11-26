/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquarePacketBinding

/-!
# Constructing the disjoint-edge loop refinements by raw gluings

The double loop is obtained from the genus-zero five-marked corolla by two
successive nonseparating gluings. The parallel-edge graph is obtained from a
rational/elliptic separating boundary, followed by nonseparating gluing of its
two ordered branch markings. Both placements of those branch markings are
retained, with the old marking on the rational component throughout.

Kernel graph-isomorphism checks bind these actual constructions to the held
raw packet columns. Existing primitive realization laws then evaluate the
already constructed five-slot expression. No product, self-pullback, or
excess-intersection identity is an input or conclusion.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSquareGluing

open AdmcyclesHodgeStrataCandidates
open scoped TensorProduct

/-- Five ordered source markings: first node pair, second node pair, old marking. -/
def doubleLoopSource :
    GluingExpression 0 (Option (Option (Option (Option (Fin 1))))) :=
  GluingExpression.fundamental 0 (Option (Option (Option (Option (Fin 1)))))
    (by unfold StableArity; decide)

/-- Close the first node pair and then the second pair, retaining the old marking. -/
def doubleLoopExpression : GluingExpression 2 (Fin 1) :=
  doubleLoopSource.nonseparating.nonseparating

/-- The rational branch becomes `none`, the elliptic branch becomes `some none`,
and the other rational marking remains the old marking. -/
def firstLabels : Fin 2 ⊕ Fin 1 ≃ Option (Option (Fin 1)) where
  toFun := Sum.elim (fun i ↦ ![none, some (some 0)] i) (fun _ ↦ some none)
  invFun
    | none => Sum.inl 0
    | some none => Sum.inr 0
    | some (some _) => Sum.inl 1
  left_inv := by
    intro x
    rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by
    intro x
    cases x with
    | none => rfl
    | some x =>
      cases x with
      | none => rfl
      | some i => fin_cases i; rfl

/-- The other ordered source placement exchanges just the two future node flags. -/
def secondLabels : Fin 2 ⊕ Fin 1 ≃ Option (Option (Fin 1)) :=
  firstLabels.trans (Equiv.swap none (some none))

/-- The genus-one separating source before either ordered branch transport. -/
def separatingSource : GluingExpression 1 (Fin 2 ⊕ Fin 1) :=
  (GluingExpression.fundamental 0 (Option (Fin 2))
    (by unfold StableArity; decide)).separating
    (GluingExpression.fundamental 1 (Option (Fin 1))
      (by unfold StableArity; decide))

/-- The old marking and first new branch lie on the rational component. -/
def parallelFirstSource : GluingExpression 1 (Option (Option (Fin 1))) :=
  separatingSource.relabel firstLabels

/-- The old marking and second new branch lie on the rational component. -/
def parallelSecondSource : GluingExpression 1 (Option (Option (Fin 1))) :=
  separatingSource.relabel secondLabels

/-- Close the two ordered branch markings of the first separating source. -/
def parallelFirstExpression : GluingExpression 2 (Fin 1) :=
  parallelFirstSource.nonseparating

/-- Close the two ordered branch markings of the second separating source. -/
def parallelSecondExpression : GluingExpression 2 (Fin 1) :=
  parallelSecondSource.nonseparating

/-- Bind all three surviving labels before the final gluing, without quotienting them. -/
theorem firstLabels_values :
    firstLabels (Sum.inl 0) = none ∧ firstLabels (Sum.inr 0) = some none ∧
      firstLabels (Sum.inl 1) = some (some 0) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Swapping future branches preserves the original external marking. -/
theorem secondLabels_values :
    secondLabels (Sum.inr 0) = none ∧ secondLabels (Sum.inl 0) = some none ∧
      secondLabels (Sum.inl 1) = some (some 0) := by
  decide +kernel

/-- The unquotiented first source has the prescribed genera and marked vertices. -/
theorem parallelFirstSource_shape :
    parallelFirstSource.graph.graph.vertexCount = 2 ∧
      parallelFirstSource.graph.graph.edgeCount = 1 ∧
      parallelFirstSource.graph.graph.genus (0 : Fin 2) = 0 ∧
      parallelFirstSource.graph.graph.genus (1 : Fin 2) = 1 ∧
      parallelFirstSource.graph.graph.legVertex none = (0 : Fin 2) ∧
      parallelFirstSource.graph.graph.legVertex (some none) = (1 : Fin 2) ∧
      parallelFirstSource.graph.graph.legVertex (some (some 0)) = (0 : Fin 2) := by
  decide +kernel

/-- The second source exchanges the ordered branches, preserving the old marking. -/
theorem parallelSecondSource_shape :
    parallelSecondSource.graph.graph.legVertex none = (1 : Fin 2) ∧
      parallelSecondSource.graph.graph.legVertex (some none) = (0 : Fin 2) ∧
      parallelSecondSource.graph.graph.legVertex (some (some 0)) = (0 : Fin 2) := by
  decide +kernel

/-- The held double-loop column is the actual composition of two raw graph maps. -/
theorem rawGraph12_eq_doubleLoop : rawGraph12 = doubleLoopExpression.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The held parallel graph is the first ordered separating/nonseparating composite. -/
theorem rawGraph28_eq_parallelFirst : rawGraph28 = parallelFirstExpression.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- The second source placement has the same held output, with its own checked map. -/
theorem rawGraph28_eq_parallelSecond : rawGraph28 = parallelSecondExpression.stratum := by
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Retain the separately decoded second packet occurrence. -/
theorem rawGraph31_eq_parallelFirst : rawGraph31 = parallelFirstExpression.stratum := by
  rw [LoopSquarePacketBinding.rawGraph31_eq_rawGraph28, rawGraph28_eq_parallelFirst]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- The actual double-loop class is two existing raw nonseparating pushforwards. -/
theorem doubleLoop_classValue (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    doubleLoopExpression.classValue F N =
      N.push 1 (Fin 1) doubleLoopExpression.stable
        (N.push 0 (Option (Option (Fin 1))) doubleLoopSource.nonseparating.stable 1) := rfl

/-- The separating source is the existing raw pushforward of the two component units. -/
theorem separatingSource_classValue (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    separatingSource.classValue F N =
      F.push 0 1 (Fin 2) (Fin 1)
        (by unfold StableArity; decide) (by unfold StableArity; decide)
        (1 ⊗ₜ[R] 1) := rfl

/-- The first parallel class retains its explicit separating source and label transport. -/
theorem parallelFirst_classValue (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) :
    parallelFirstExpression.classValue F N =
      N.push 1 (Fin 1) parallelFirstExpression.stable
        (C.rename 1 (Fin 2 ⊕ Fin 1) (Option (Option (Fin 1)))
          separatingSource.stable parallelFirstSource.stable firstLabels
          (separatingSource.classValue F N)) := rfl

/-- Existing primitive realization laws evaluate the actual five packet slots.
This is the image of a constructed linear expression, not a boundary product law. -/
theorem map_packetPart
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C)
    (hglue : (A 1 (Option (Option (Fin 1)))).NonseparatingCompatible
      (A 2 (Fin 1)) N HodgeDegreeOneRealization.stable)
    (hpsi : (A 1 (Option (Option (Fin 1)))).LegPsiCompatible P
      (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable))
    (hfund : (A 1 (Option (Option (Fin 1)))).map
      (StrataModule.basis HodgeNodeNormal.source) = 1)
    (hdouble : doubleLoopExpression.Compatible A F N)
    (hparallel : parallelFirstExpression.Compatible A F N) :
    (A 2 (Fin 1)).map LoopSquarePacketBinding.packetPart = (1 / 24 : ℚ) ^ 2 •
      ((2 : ℚ) • N.push 1 (Fin 1) HodgeDegreeOneRealization.stable
        (-(P.psi 1 (Option (Option (Fin 1)))
            (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable) none +
          P.psi 1 (Option (Option (Fin 1)))
            (StableArity.double_option_iff.mpr HodgeDegreeOneRealization.stable) (some none))) +
        doubleLoopExpression.classValue F N +
        (4 : ℚ) • parallelFirstExpression.classValue F N) := by
  rw [LoopSquarePacketBinding.packetPart_eq_scaled_refinement,
    LoopSquarePacketBinding.refinementExpression_eq, map_smul, map_add, map_add,
    map_smul, map_smul,
    (A 1 (Option (Option (Fin 1)))).map_nonseparatingNodeNormal (A 2 (Fin 1)) N P
      HodgeDegreeOneRealization.stable hglue hpsi,
    hfund, one_mul, rawGraph12_eq_doubleLoop, rawGraph28_eq_parallelFirst,
    doubleLoopExpression.map_stratum_eq_classValue A F N hdouble,
    parallelFirstExpression.map_stratum_eq_classValue A F N hparallel]

end AxiomaticGW.GKM.LoopSquareGluing
