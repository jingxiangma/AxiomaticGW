/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW

set_option linter.privateModule false

/-!
# Nonseparating graph and boundary evaluation regressions

These examples test loop and parallel-edge gluing, asymmetric node powers,
fixed labels, changed automorphism orders, coefficient merging, degree and
certificate transfer, and the actual inverse-metric ancestor contraction.
The constant-target test explicitly rejects an incompatible Gysin package;
no synthetic constant target is claimed to model geometric boundary classes.
-/

namespace AxiomaticGWTest.Tautological.Nonseparating

open AxiomaticGW

private theorem loopSourceStable : StableArity 1 (Option (Option (Fin 0))) := by
  norm_num only [StableArity, Fintype.card_option, Fintype.card_fin]

private def loopSource (a b : ℕ) : DecoratedStableGraph (Option (Option (Fin 0))) :=
  DecoratedStableGraph.oneVertex 1 _ loopSourceStable 0
    (fun | none => a | some none => b | some (some s) => Fin.elim0 s)

private def loopStratum (a b : ℕ) : TautologicalStratum 1 (Option (Option (Fin 0))) :=
  TautologicalStratum.mk (loopSource a b)
    (DecoratedStableGraph.oneVertex_totalGenus 1 _ loopSourceStable 0 _)

/-- Both branches of the new loop meet the old vertex, whose genus stays one. -/
example : (loopSource 2 3).nonseparating.graph.vertexCount = 1 ∧
    (loopSource 2 3).nonseparating.graph.edgeCount = 1 ∧
    (loopSource 2 3).nonseparating.graph.genus ⟨0, by decide⟩ = 1 ∧
    (loopSource 2 3).nonseparating.graph.totalGenus = 2 ∧
    (loopSource 2 3).nonseparating.graph.endpoint ⟨0, by decide⟩ 0 = ⟨0, by decide⟩ ∧
    (loopSource 2 3).nonseparating.graph.endpoint ⟨0, by decide⟩ 1 = ⟨0, by decide⟩ := by decide

/-- Unequal node powers survive gluing in the declared branch order. -/
example : (loopSource 2 3).nonseparating.halfEdgePsiPower ⟨0, by decide⟩ 0 = 2 ∧
    (loopSource 2 3).nonseparating.halfEdgePsiPower ⟨0, by decide⟩ 1 = 3 ∧
    (loopSource 2 3).nonseparating.codimension = 6 := by decide

/-- A new loop flip creates an automorphism absent from the labelled source. -/
example : (loopSource 0 0).automorphismCount = 1 ∧
    (loopSource 0 0).nonseparating.automorphismCount = 2 := by decide

/-- Unequal branch powers remove that flip in the decorated graph. -/
example : (loopSource 2 3).nonseparating.automorphismCount = 1 := by decide

private theorem sourceLabelsDifferent : loopStratum 1 0 ≠ loopStratum 0 1 := by
  intro h
  obtain ⟨e⟩ := Quotient.exact h
  have hc := e.legPsiPower_comm none
  exact (by decide : (0 : ℕ) ≠ 1) hc

private theorem gluedLabelsEqual :
    (loopStratum 1 0).nonseparating = (loopStratum 0 1).nonseparating := by
  change TautologicalStratum.mk (loopSource 1 0).nonseparating _ =
    TautologicalStratum.mk (loopSource 0 1).nonseparating _
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  decide

/-- Distinct source markings become interchangeable internal branches;
the quotient gluing map is not injective. -/
example : ¬Function.Injective
    (fun x : TautologicalStratum 1 (Option (Option (Fin 0))) ↦ x.nonseparating) := by
  intro h
  exact sourceLabelsDifferent (h gluedLabelsEqual)

/-- Coincident output classes receive the sum of their unchanged raw
coefficients, even though their automorphism orders may change. -/
example : StrataModule.nonseparating
    ((3 : ℚ) • StrataModule.basis (loopStratum 1 0) +
      (-1 / 2 : ℚ) • StrataModule.basis (loopStratum 0 1)) =
    (5 / 2 : ℚ) • StrataModule.basis (loopStratum 1 0).nonseparating := by
  rw [map_add, map_smul, map_smul, StrataModule.nonseparating_basis,
    StrataModule.nonseparating_basis, ← gluedLabelsEqual, ← add_smul]
  norm_num

private def parallelSourceGraph : StableGraphCode (Option (Option (Fin 2))) where
  vertexCount := 2
  edgeCount := 1
  vertexCount_pos := by decide
  legVertex := fun | none => 0 | some none => 1 | some (some _) => 0
  endpoint := fun _ ↦ ![0,1]
  genus := ![0,1]
  connected := by
    intro v w
    fin_cases v <;> fin_cases w
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.single ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.refl
  stable := by intro v; fin_cases v <;> decide

private def parallelSource : DecoratedStableGraph (Option (Option (Fin 2))) where
  graph := parallelSourceGraph
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ _ ↦ 0

/-- Joining distinct vertices in a connected graph can create a parallel
edge, giving a genus-two stratum without changing vertex genera. -/
example : parallelSource.nonseparating.graph.vertexCount = 2 ∧
    parallelSource.nonseparating.graph.edgeCount = 2 ∧
    parallelSource.nonseparating.graph.totalGenus = 2 ∧
    parallelSource.nonseparating.graph.endpoint ⟨0, by decide⟩ 0 = ⟨0, by decide⟩ ∧
    parallelSource.nonseparating.graph.endpoint ⟨1, by decide⟩ 0 = ⟨0, by decide⟩ ∧
    parallelSource.nonseparating.graph.endpoint ⟨0, by decide⟩ 1 = ⟨1, by decide⟩ ∧
    parallelSource.nonseparating.graph.endpoint ⟨1, by decide⟩ 1 = ⟨1, by decide⟩ := by decide

/-- The two parallel edges become interchangeable; gluing does not preserve
the source automorphism count. -/
example : parallelSource.automorphismCount = 1 ∧
    parallelSource.nonseparating.automorphismCount = 2 := by decide

private noncomputable def decoratedParallelSource :
    DecoratedStableGraph (Option (Option (Fin 2))) where
  graph := parallelSourceGraph
  kappaPower := fun _ ↦ Finsupp.single ⟨2, by decide⟩ 1
  legPsiPower := fun | none => 2 | some none => 3 | some (some s) => ![5,7] s
  halfEdgePsiPower := fun _ ↦ ![11,13]

/-- Existing internal decorations, retained marking labels, and both vertex
kappa powers survive while the node powers move to the new last edge. -/
example : decoratedParallelSource.nonseparating.halfEdgePsiPower ⟨0, by decide⟩ 0 = 11 ∧
    decoratedParallelSource.nonseparating.halfEdgePsiPower ⟨0, by decide⟩ 1 = 13 ∧
    decoratedParallelSource.nonseparating.halfEdgePsiPower ⟨1, by decide⟩ 0 = 2 ∧
    decoratedParallelSource.nonseparating.halfEdgePsiPower ⟨1, by decide⟩ 1 = 3 ∧
    decoratedParallelSource.nonseparating.legPsiPower 0 = 5 ∧
    decoratedParallelSource.nonseparating.legPsiPower 1 = 7 ∧
    decoratedParallelSource.nonseparating.kappaPower ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 ∧
    decoratedParallelSource.nonseparating.codimension = 47 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact Finsupp.single_eq_same
  · rw [DecoratedStableGraph.nonseparating_codimension]
    have hk : decoratedParallelSource.kappaCodimension = 4 := by
      change (∑ _v : Fin 2, (Finsupp.single (⟨2, by decide⟩ : ℕ+) 1).sum
        (fun i power ↦ (i : ℕ) * power)) = 4
      norm_num only [Fin.sum_univ_two, Finsupp.sum_single_index, mul_zero, mul_one]
    have hl : decoratedParallelSource.legPsiCodimension = 17 := by decide
    have he : decoratedParallelSource.halfEdgePsiCodimension = 24 := by decide
    rw [DecoratedStableGraph.codimension, hk, hl, he]
    decide

/-- Graph isomorphisms, including old loop flips and edge permutations, lift
to the gluing construction without assuming uniqueness of the lift. -/
example {S : Type} [Fintype S] {G H : DecoratedStableGraph (Option (Option S))}
    (e : DecoratedStableGraph.Iso G H) :
    Nonempty (DecoratedStableGraph.Iso G.nonseparating H.nonseparating) := ⟨e.nonseparating⟩

/-- Above-dimension source relations remain above dimension at genus two. -/
example (r : StrataModule 1 (Option (Option (Fin 0))))
    (hr : r ∈ StrataModule.dimensionRelations) :
    StrataModule.nonseparating r ∈ StrataModule.dimensionRelations :=
  StrataModule.nonseparating_mem_dimensionRelations
    (by norm_num only [StableArity, Fintype.card_fin]) hr

attribute [local instance] strataRealizationModule

/-- Actual graph multiplication, raw gluing, and cohomological evaluation
compose to the existing class-resolved GW ancestor contraction. Only
primitive realization laws and fundamental normalization are supplied. -/
example {R V Bclass : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid Bclass] {D : EffectiveCurveMonoid Bclass}
    {C : StableCurveCohomology R} (I : StableCurveIntegration C)
    (P : PsiClasses C) (F : NonseparatingPushforward C I)
    (A : StrataRealization C 1 (Option (Option (Fin 2))))
    (B : StrataRealization C 2 (Fin 2))
    (h : StableArity 2 (Fin 2)) (hAB : A.NonseparatingCompatible B F h)
    (hP : A.LegPsiCompatible P (StableArity.double_option_iff.mpr h))
    (hfund : A.map (StrataModule.basis (TautologicalStratum.fundamental
      1 (Option (Option (Fin 2))) (StableArity.double_option_iff.mpr h))) = 1)
    (Omega : GromovWittenTheory R V Bclass D C)
    (beta : Bclass) (k : Option (Option (Fin 2)) → ℕ) (a : Fin 2 → V) :
    B.integrateAgainst I h (Omega.omega 2 (Fin 2) h beta a)
      (StrataModule.nonseparating (StrataModule.mulLegPsi k
        (StrataModule.basis (TautologicalStratum.fundamental
          1 (Option (Option (Fin 2))) (StableArity.double_option_iff.mpr h))))) =
    Omega.pairing.selfContract
      ((Omega.ancestorInvariant P I 1 (Option (Option (Fin 2)))
        (StableArity.double_option_iff.mpr h) beta k).domDomCongr
          (doubleOptionEquiv (Fin 2))) a := by
  rw [A.integrateAgainst_nonseparating_gw B F h hAB Omega beta a,
    A.map_mulLegPsi P _ hP, hfund, one_mul, Omega.nonseparatingInvariant_monomial]

private def dimensionRows : Fin 1 → RelationCertificate.Coordinates 2 := fun _ ↦ ![1,-1]

private def dimensionCertificate : RelationCertificate.Certificate 1 := ⟨![2]⟩

private theorem dimensionCheck :
    RelationCertificate.check dimensionRows ![2,-2] dimensionCertificate = true := by
  rw [RelationCertificate.check_eq_true_iff]
  funext i
  fin_cases i <;>
    norm_num only [RelationCertificate.combination, dimensionRows, dimensionCertificate,
      Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.zero_eta, Fin.mk_one]

/-- The certificate below has distinct output columns, so its equation
cannot pass solely by cancelling identical glued graph classes. -/
private theorem gluedDimensionColumnsDifferent :
    (loopStratum 3 0).nonseparating ≠ (loopStratum 2 1).nonseparating := by
  intro h
  change TautologicalStratum.mk (loopSource 3 0).nonseparating _ =
    TautologicalStratum.mk (loopSource 2 1).nonseparating _ at h
  obtain ⟨e⟩ := Quotient.exact h
  have hc := e.halfEdgePsiPower_comm ⟨0, by decide⟩ 0
  have hne : ∀ (edge : Fin (loopSource 2 1).nonseparating.graph.edgeCount) (i : Fin 2),
      (loopSource 2 1).nonseparating.halfEdgePsiPower edge i ≠ 3 := by decide
  exact hne _ _ hc

/-- The fixed certificate uses actual dimension-vanishing source rows.
Its glued integrated consequence needs no separately assumed numerical row. -/
example {R : Type} [CommRing R] [Algebra ℚ R] {C : StableCurveCohomology R}
    (I : StableCurveIntegration C) (F : NonseparatingPushforward C I)
    (A : StrataRealization C 1 (Option (Option (Fin 0))))
    (B : StrataRealization C 2 (Fin 0)) (h : StableArity 2 (Fin 0))
    (hAB : A.NonseparatingCompatible B F h) (w : C.H 2 (Fin 0)) :
    (∑ i : Fin 2, (![2,-2] i : ℚ) • I.integrate 2 (Fin 0) h
      (w * B.map (StrataModule.basis
        ((![loopStratum 3 0, loopStratum 2 1] i).nonseparating)))) = 0 := by
  apply A.certificate_nonseparating_eq_zero B F h hAB w
    ![loopStratum 3 0, loopStratum 2 1] dimensionRows ![2,-2]
    dimensionCertificate dimensionCheck
  have hz : ∀ i : Fin 2,
      A.map (StrataModule.basis (![loopStratum 3 0, loopStratum 2 1] i)) = 0 := by
    intro i
    apply C.eq_zero_of_dimension_lt 1 (Option (Option (Fin 0)))
      loopSourceStable _ _ (A.map_basis_degree _)
    fin_cases i <;> decide
  intro row
  rw [RelationCertificate.interpret_apply, Fin.sum_univ_two, map_add, map_smul, map_smul]
  rw [hz 0, hz 1, smul_zero, smul_zero, zero_add]

private noncomputable def rankTwoCohFT :
    CohFT ℚ (ℚ × ℚ) (constantStableCurveCohomology ℚ) :=
  (CommFrobeniusAlgebra.productAlgebra ℚ).toTopologicalCohFT.toConstantCohFT

/-- A nonzero two-dimensional state-space example checks the ancestor
contraction itself. It is a CohFT fixture, not a geometric boundary model. -/
example : rankTwoCohFT.pairing.selfContract
    ((rankTwoCohFT.ancestor (constantStableCurveCohomology.psiClasses ℚ)
      (constantStableCurveCohomology.integration ℚ) 0 (Option (Option (Fin 1)))
      (by norm_num only [StableArity, Fintype.card_option, Fintype.card_fin])
      (fun _ ↦ 0)).domDomCongr (doubleOptionEquiv (Fin 1))) ![(2,3)] = 5 := by
  have h : StableArity 1 (Fin 1) := by norm_num only [StableArity, Fintype.card_fin]
  have ha : rankTwoCohFT.ancestor (constantStableCurveCohomology.psiClasses ℚ)
      (constantStableCurveCohomology.integration ℚ) 0 (Option (Option (Fin 1)))
      (StableArity.double_option_iff.mpr h) (fun _ ↦ 0) =
      rankTwoCohFT.omega 0 (Option (Option (Fin 1)))
        (StableArity.double_option_iff.mpr h) := by
    ext a
    rw [CohFT.ancestor_zero_apply]
    rfl
  rw [ha, ← SymmetricPerfectPairing.selfContractTarget_eq_selfContract,
    rankTwoCohFT.nonseparating 0 (Fin 1) h]
  change (CommFrobeniusAlgebra.productAlgebra ℚ).correlator 1 (Fin 1) ![(2,3)] = 5
  rw [CommFrobeniusAlgebra.correlator_apply, CommFrobeniusAlgebra.productAlgebra_handleElement]
  norm_num only [Fin.prod_univ_one, Matrix.cons_val_fin_one, pow_one, mul_one,
    CommFrobeniusAlgebra.productCounit_apply]
  change (2 : ℚ) + 3 = 5
  norm_num

/-- A degree-zero constant cohomology target with nonzero integration on
Mbar(0,3) cannot carry the geometric nonseparating Gysin package. This
prevents using it as a fake boundary model with vacuous numerical tests. -/
example : ¬Nonempty (NonseparatingPushforward (constantStableCurveCohomology ℚ)
    (constantStableCurveCohomology.integration ℚ)) := by
  rintro ⟨F⟩
  have h : StableArity 1 (Fin 1) := by norm_num only [StableArity, Fintype.card_fin]
  have hp := F.push_degree 0 (Fin 1) h 0 1 SetLike.GradedOne.one_mem
  have hz : F.push 0 (Fin 1) h 1 = 0 := by
    change _ ∈ (⊥ : Submodule ℚ ℚ) at hp
    exact (Submodule.mem_bot ℚ).mp hp
  have hi := F.integrate_push 0 (Fin 1) h 1
  rw [hz, map_zero] at hi
  change (0 : ℚ) = 1 at hi
  exact zero_ne_one hi

end AxiomaticGWTest.Tautological.Nonseparating
