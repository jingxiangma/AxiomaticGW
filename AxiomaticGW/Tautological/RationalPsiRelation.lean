/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.PsiBoundaryExpansion

/-!
# Genus-zero psi relations in the free strata module

The source psi on Mbar(0,3) vanishes by dimension. The existing universal-curve
formula derives its higher-arity boundary expansion. This file records that
equation in the free strata module so it can be inserted into a decorated
component of a larger graph. No new geometric relation is required.
-/

@[expose] public section

namespace AxiomaticGW.RationalPsiRelation
open PsiBoundaryExpansion

/-- The psi term at the original first label after adding markings. -/
def leading (n : ℕ) : DecoratedStableGraph (ExtraMarkings n (Fin 3)) :=
  letI := ExtraMarkings.decidableEq (Fin 3) n
  DecoratedStableGraph.oneVertex 0 _ (StableArity.zero_fin_three.extraMarkings n) 0
    (Pi.single (ExtraMarkings.oldLabel n 0) 1)

/-- The cotangent term has genus zero. -/
theorem leading_totalGenus (n : ℕ) : (leading n).graph.totalGenus = 0 :=
  DecoratedStableGraph.oneVertex_totalGenus _ _ _ _ _

/-- The complete signed source relation, before any component is attached. -/
noncomputable def relation (n : ℕ) : StrataModule 0 (ExtraMarkings n (Fin 3)) :=
  StrataModule.basis (.mk (leading n) (leading_totalGenus n)) -
    ((genusZeroTerms 0 n).map fun t ↦ t.1 • StrataModule.basis t.2.stratum).sum

/-- One leading column and every boundary term, including its original multiplicity. -/
abbrev size (n : ℕ) : ℕ := (genusZeroTerms 0 n).length + 1

/-- Old labels come first; the original first marking carries the leading psi. -/
def graph (n : ℕ) : Fin (size n) → DecoratedStableGraph (Fin (3 + n)) :=
  Fin.cases ((leading n).relabel (ExtraMarkings.finEquiv n 3)) fun i ↦
    ((genusZeroTerms 0 n)[i.val].2.graph).relabel (ExtraMarkings.finEquiv n 3)

/-- Every finite source column has genus zero. -/
theorem graph_totalGenus (n : ℕ) (i : Fin (size n)) : (graph n i).graph.totalGenus = 0 := by
  cases i using Fin.cases with
  | zero => exact leading_totalGenus n
  | succ i => exact (genusZeroTerms 0 n)[i.val].2.graph_totalGenus

/-- Quotient columns of the actual genus-zero expansion. -/
def columns (n : ℕ) (i : Fin (size n)) : TautologicalStratum 0 (Fin (3 + n)) :=
  .mk (graph n i) (graph_totalGenus n i)

/-- Leading coefficient one and the negatives of the derived boundary weights. -/
def coordinates (n : ℕ) : RelationCertificate.Coordinates (size n) :=
  Fin.cases 1 fun i ↦ -(genusZeroTerms 0 n)[i.val].1

/-- The finite frame is the actual derived relation with its labels enumerated. -/
theorem interpret_coordinates (n : ℕ) :
    RelationCertificate.interpret (columns n) (coordinates n) =
      StrataModule.relabel (ExtraMarkings.finEquiv n 3) (relation n) := by
  rw [RelationCertificate.interpret_apply]
  change (∑ i : Fin ((genusZeroTerms 0 n).length + 1),
    coordinates n i • StrataModule.basis (columns n i)) = _
  rw [Fin.sum_univ_succ]
  simp only [coordinates, Fin.cases_zero, Fin.cases_succ, one_smul, neg_smul,
    Finset.sum_neg_distrib, relation, map_sub, map_list_sum, List.map_map,
    Function.comp_def, map_smul, StrataModule.relabel_basis]
  rw [← sub_eq_add_neg]
  change StrataModule.basis _ - ∑ i : Fin (genusZeroTerms 0 n).length,
      (genusZeroTerms 0 n)[i.val].1 • StrataModule.basis
        ((genusZeroTerms 0 n)[i.val].2.stratum.relabel (ExtraMarkings.finEquiv n 3)) = _
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map (genusZeroTerms 0 n)
    (fun t ↦ t.1 • StrataModule.basis (t.2.stratum.relabel (ExtraMarkings.finEquiv n 3)))]
  rfl

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The primitive psi and graph laws prove the entire free-module source relation. -/
theorem realized_relation (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (P : PsiClasses C) (K : PsiForgetFormula P)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hK : TailCompatible K F N) (n : ℕ)
    (hp : (A 0 (ExtraMarkings n (Fin 3))).LegPsiCompatible P
      (StableArity.zero_fin_three.extraMarkings n))
    (hf : (A 0 (ExtraMarkings n (Fin 3))).map (StrataModule.basis
      (TautologicalStratum.fundamental 0 _ (StableArity.zero_fin_three.extraMarkings n))) = 1)
    (hb : ∀ t ∈ genusZeroTerms 0 n, t.2.Compatible A F N) :
    (A 0 (ExtraMarkings n (Fin 3))).map (relation n) = 0 := by
  letI := ExtraMarkings.decidableEq (Fin 3) n
  have hl : TautologicalStratum.mk (leading n) (leading_totalGenus n) =
      (TautologicalStratum.fundamental 0 _ (StableArity.zero_fin_three.extraMarkings n)).addLegPsi
        (Pi.single (ExtraMarkings.oldLabel n 0) 1) := by
    rw [TautologicalStratum.fundamental, TautologicalStratum.addLegPsi_oneVertex]
    change TautologicalStratum.oneVertex _ _ _ _ _ =
      TautologicalStratum.oneVertex _ _ _ _ ((0 : ExtraMarkings n (Fin 3) → ℕ) + _)
    rw [zero_add]
  have hv : (A 0 (ExtraMarkings n (Fin 3))).map
      (((genusZeroTerms 0 n).map fun t ↦ t.1 • StrataModule.basis t.2.stratum).sum) =
      value F N (genusZeroTerms 0 n) := by
    simp only [map_list_sum, List.map_map, Function.comp_def, map_smul, value]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    rw [t.2.map_stratum_eq_classValue A F N (hb t ht)]
  rw [relation, map_sub, hl, StrataRealization.map_addLegPsi_one _ P _ hp, hf, one_mul,
    hv, genusZero_psi_eq_value P K F N H hK, sub_self]

/-- The same proved source equation in the finite coordinate frame. -/
theorem realized_coordinates (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (P : PsiClasses C) (K : PsiForgetFormula P)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hK : TailCompatible K F N) (n : ℕ)
    (hp : (A 0 (ExtraMarkings n (Fin 3))).LegPsiCompatible P
      (StableArity.zero_fin_three.extraMarkings n))
    (hf : (A 0 (ExtraMarkings n (Fin 3))).map (StrataModule.basis
      (TautologicalStratum.fundamental 0 _ (StableArity.zero_fin_three.extraMarkings n))) = 1)
    (hb : ∀ t ∈ genusZeroTerms 0 n, t.2.Compatible A F N)
    (hl : (A 0 (ExtraMarkings n (Fin 3))).RelabelCompatible (A 0 (Fin (3 + n)))
      (StableArity.zero_fin_three.extraMarkings n)
      ((StableArity.equiv (ExtraMarkings.finEquiv n 3)).mp
        (StableArity.zero_fin_three.extraMarkings n)) (ExtraMarkings.finEquiv n 3)) :
    (A 0 (Fin (3 + n))).map
      (RelationCertificate.interpret (columns n) (coordinates n)) = 0 := by
  rw [interpret_coordinates, StrataRealization.map_relabel _ _ _ _ _ hl,
    realized_relation A P K F N H hK n hp hf hb, map_zero]

end AxiomaticGW.RationalPsiRelation
