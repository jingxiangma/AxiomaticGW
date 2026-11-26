/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW

set_option linter.privateModule false

/-!
# Separating graph, certificate, and ancestor regressions

The examples include interchangeable components, loop automorphisms,
asymmetric decorations, exact certificates with distinct output graphs,
and full effective-class splitting. A nonzero rank-two CohFT checks the
component contraction. It is not a surface GW value or a geometric Gysin
model; the negative example excludes the constant target as such a model.
-/

namespace AxiomaticGWTest.Tautological.Separating

open AxiomaticGW TensorProduct

private theorem bareStable : StableArity 1 (Option (Fin 0)) := by
  norm_num only [StableArity, Fintype.card_option, Fintype.card_fin]

private theorem rightStable : StableArity 2 (Option (Fin 0)) := by
  norm_num only [StableArity, Fintype.card_option, Fintype.card_fin]

private theorem targetStable : StableArity 2 (Fin 2 ⊕ Fin 0) :=
  StableArity.separating StableArity.zero_option_fin_two rightStable

private def bare (a : ℕ) : DecoratedStableGraph (Option (Fin 0)) :=
  DecoratedStableGraph.oneVertex 1 _ bareStable 0 (fun _ ↦ a)

private noncomputable def bareStratum (a : ℕ) : TautologicalStratum 1 (Option (Fin 0)) :=
  TautologicalStratum.mk (bare a) (DecoratedStableGraph.oneVertex_totalGenus ..)

/-- Two unmarked genus-one vertices yield the genus-two separating boundary. -/
example : ((bare 2).separating (bare 3)).graph.vertexCount = 2 ∧
    ((bare 2).separating (bare 3)).graph.edgeCount = 1 ∧
    ((bare 2).separating (bare 3)).graph.totalGenus = 2 ∧
    ((bare 2).separating (bare 3)).halfEdgePsiPower ⟨0, by decide⟩ 0 = 2 ∧
    ((bare 2).separating (bare 3)).halfEdgePsiPower ⟨0, by decide⟩ 1 = 3 ∧
    ((bare 2).separating (bare 3)).codimension = 6 := by decide

/-- Equal undecorated components create a new exchange automorphism. -/
example : (bare 0).automorphismCount = 1 ∧
    ((bare 0).separating (bare 0)).automorphismCount = 2 := by decide

/-- Unequal node powers break that component exchange. -/
example : ((bare 2).separating (bare 3)).automorphismCount = 1 := by decide

private theorem swappedBareEqual :
    (bareStratum 2).separating (bareStratum 3) =
      (bareStratum 3).separating (bareStratum 2) := by
  change TautologicalStratum.mk ((bare 2).separating (bare 3)) _ =
    TautologicalStratum.mk ((bare 3).separating (bare 2)) _
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  decide

/-- Raw coefficients remain unchanged even when the output has automorphisms. -/
example : StrataModule.separating ((3 : ℚ) • StrataModule.basis (bareStratum 0))
    ((2 : ℚ) • StrataModule.basis (bareStratum 0)) =
      (6 : ℚ) • StrataModule.basis ((bareStratum 0).separating (bareStratum 0)) := by
  simp only [map_smul, LinearMap.smul_apply,
    StrataModule.separating_basis_basis, smul_smul]
  norm_num only

/-- Different ordered component pairs may give the same quotient graph;
their signed coefficients add without a normalization factor. -/
example : (3 : ℚ) • StrataModule.separating (StrataModule.basis (bareStratum 2))
      (StrataModule.basis (bareStratum 3)) +
    (-1 / 2 : ℚ) • StrataModule.separating (StrataModule.basis (bareStratum 3))
      (StrataModule.basis (bareStratum 2)) =
    (5 / 2 : ℚ) • StrataModule.basis ((bareStratum 2).separating (bareStratum 3)) := by
  rw [StrataModule.separating_basis_basis, StrataModule.separating_basis_basis,
    ← swappedBareEqual, ← add_smul]
  norm_num only

private def loopGraph : StableGraphCode (Option (Fin 0)) where
  vertexCount := 1
  edgeCount := 1
  vertexCount_pos := by decide
  legVertex := fun _ ↦ 0
  endpoint := fun _ _ ↦ 0
  genus := fun _ ↦ 0
  connected := by
    intro v w
    have hvw : v = w := Subsingleton.elim _ _
    subst w
    exact .refl
  stable := by
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    decide

private def loop (node a b : ℕ) : DecoratedStableGraph (Option (Fin 0)) where
  graph := loopGraph
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ node
  halfEdgePsiPower := fun _ ↦ ![a,b]

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all 96 candidate graph automorphisms.
/-- Old loops stay loops, and the new edge joins their distinct vertices. -/
example : ((loop 0 0 0).separating (loop 0 0 0)).graph.vertexCount = 2 ∧
    ((loop 0 0 0).separating (loop 0 0 0)).graph.edgeCount = 3 ∧
    ((loop 0 0 0).separating (loop 0 0 0)).graph.totalGenus = 2 ∧
    ((loop 0 0 0).separating (loop 0 0 0)).automorphismCount = 8 := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all 96 candidate decorated automorphisms.
/-- Both internal flags of each old loop and both new node powers survive. -/
example : ((loop 2 11 13).separating (loop 3 17 19)).halfEdgePsiPower
      ⟨0, by decide⟩ 0 = 11 ∧
    ((loop 2 11 13).separating (loop 3 17 19)).halfEdgePsiPower
      ⟨0, by decide⟩ 1 = 13 ∧
    ((loop 2 11 13).separating (loop 3 17 19)).halfEdgePsiPower
      ⟨1, by decide⟩ 0 = 17 ∧
    ((loop 2 11 13).separating (loop 3 17 19)).halfEdgePsiPower
      ⟨1, by decide⟩ 1 = 19 ∧
    ((loop 2 11 13).separating (loop 3 17 19)).halfEdgePsiPower
      ⟨2, by decide⟩ 0 = 2 ∧
    ((loop 2 11 13).separating (loop 3 17 19)).halfEdgePsiPower
      ⟨2, by decide⟩ 1 = 3 ∧
    ((loop 2 11 13).separating (loop 3 17 19)).automorphismCount = 1 := by decide

private noncomputable def markedLeft : DecoratedStableGraph (Option (Fin 2)) :=
  DecoratedStableGraph.oneVertex 0 _ StableArity.zero_option_fin_two
    (Finsupp.single ⟨1, by decide⟩ 2) (fun | none => 2 | some i => ![5,7] i)

private noncomputable def markedRight : DecoratedStableGraph (Option (Fin 2)) :=
  DecoratedStableGraph.oneVertex 2 _
    (by norm_num only [StableArity, Fintype.card_option, Fintype.card_fin])
    (Finsupp.single ⟨2, by decide⟩ 1) (fun | none => 3 | some i => ![11,13] i)

/-- Retained labels and unequal vertex kappa indices cannot be exchanged. -/
example : (markedLeft.separating markedRight).legPsiPower (.inl 0) = 5 ∧
    (markedLeft.separating markedRight).legPsiPower (.inl 1) = 7 ∧
    (markedLeft.separating markedRight).legPsiPower (.inr 0) = 11 ∧
    (markedLeft.separating markedRight).legPsiPower (.inr 1) = 13 ∧
    (markedLeft.separating markedRight).kappaPower ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 ∧
    (markedLeft.separating markedRight).kappaPower ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 ∧
    (markedLeft.separating markedRight).graph.totalGenus = 2 ∧
    (markedLeft.separating markedRight).codimension = 46 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, by decide, ?_⟩
  · change (Finsupp.single (⟨1, by decide⟩ : ℕ+) 2) ⟨1, by decide⟩ = 2
    exact Finsupp.single_eq_same
  · change (Finsupp.single (⟨2, by decide⟩ : ℕ+) 1) ⟨2, by decide⟩ = 1
    exact Finsupp.single_eq_same
  · rw [DecoratedStableGraph.separating_codimension]
    norm_num only [markedLeft, markedRight, DecoratedStableGraph.oneVertex_codimension,
      Finsupp.sum_single_index, mul_zero, Fintype.sum_option, Fin.sum_univ_two,
      PNat.mk_coe, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Independent isomorphisms descend without assuming equality of presentations. -/
example {S T : Type} [Fintype S] [Fintype T]
    {G G' : DecoratedStableGraph (Option S)} {H H' : DecoratedStableGraph (Option T)}
    (e : DecoratedStableGraph.Iso G G') (f : DecoratedStableGraph.Iso H H') :
    Nonempty (DecoratedStableGraph.Iso (G.separating H) (G'.separating H')) :=
  ⟨e.separating f⟩

private noncomputable def leftColumn (node : Bool) : TautologicalStratum 0 (Option (Fin 2)) :=
  TautologicalStratum.oneVertex 0 _ StableArity.zero_option_fin_two 0
    (if node then (fun | none => 1 | some _ => 0)
      else (fun | none => 0 | some i => if i = 0 then 1 else 0))

private noncomputable def rightColumn : TautologicalStratum 2 (Option (Fin 0)) :=
  TautologicalStratum.fundamental 2 _ rightStable

private theorem gluedColumnsDifferent :
    (leftColumn true).separating rightColumn ≠ (leftColumn false).separating rightColumn := by
  intro h
  obtain ⟨e⟩ := Quotient.exact h
  have hp := e.legPsiPower_comm (.inl 0)
  exact (by decide : (1 : ℕ) ≠ 0) hp

/-- The vanishing source columns glue below the target dimension bound.
Their vanishing therefore requires geometric composition. -/
example : (leftColumn true).codimension > StableArity.dimension 0 (Option (Fin 2)) ∧
    (leftColumn false).codimension > StableArity.dimension 0 (Option (Fin 2)) ∧
    ((leftColumn true).separating rightColumn).codimension ≤
      StableArity.dimension 2 (Fin 2 ⊕ Fin 0) := by decide

private def rows : Fin 1 → RelationCertificate.Coordinates 2 := fun _ ↦ ![1,-1]
private def witness : RelationCertificate.Certificate 1 := ⟨![2]⟩

private theorem check : RelationCertificate.check rows ![2,-2] witness = true := by
  rw [RelationCertificate.check_eq_true_iff]
  funext i
  fin_cases i <;>
    norm_num only [RelationCertificate.combination, rows, witness, Fin.sum_univ_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.zero_eta, Fin.mk_one]

attribute [local instance] strataRealizationModule

/-- The fixed exact row and original dimension vanishing prove a glued
equation with distinct output graphs and an arbitrary held upper class. -/
example {R : Type} [CommRing R] [Algebra ℚ R] {C : StableCurveCohomology R}
    (I : StableCurveIntegration C) (F : SeparatingPushforward C I)
    (A : StrataRealization C 0 (Option (Fin 2)))
    (B : StrataRealization C 2 (Option (Fin 0)))
    (U : StrataRealization C 2 (Fin 2 ⊕ Fin 0))
    (hAB : A.SeparatingCompatible B U F StableArity.zero_option_fin_two rightStable)
    (w : C.H 2 (Fin 2 ⊕ Fin 0)) :
    (∑ i : Fin 2, (![2,-2] i : ℚ) • I.integrate 2 (Fin 2 ⊕ Fin 0) targetStable
      (w * U.map (StrataModule.basis
        ((![leftColumn true, leftColumn false] i).separating rightColumn)))) = 0 := by
  apply A.certificate_separating_left_eq_zero B U F StableArity.zero_option_fin_two
    rightStable hAB w ![leftColumn true, leftColumn false] rows ![2,-2] witness check
    (y := rightColumn)
  have hz : ∀ i : Fin 2,
      A.map (StrataModule.basis (![leftColumn true, leftColumn false] i)) = 0 := by
    intro i
    apply C.eq_zero_of_dimension_lt 0 (Option (Fin 2))
      StableArity.zero_option_fin_two _ _ (A.map_basis_degree _)
    fin_cases i <;> decide
  intro row
  rw [RelationCertificate.interpret_apply, Fin.sum_univ_two, map_add, map_smul, map_smul,
    hz 0, hz 1, smul_zero, smul_zero, zero_add]

/-- The same original certificate transfers when its vanishing component
is on the right, with all retained labels in the second target block. -/
example {R : Type} [CommRing R] [Algebra ℚ R] {C : StableCurveCohomology R}
    (I : StableCurveIntegration C) (F : SeparatingPushforward C I)
    (A : StrataRealization C 2 (Option (Fin 0)))
    (B : StrataRealization C 0 (Option (Fin 2)))
    (U : StrataRealization C 2 (Fin 0 ⊕ Fin 2))
    (hAB : A.SeparatingCompatible B U F rightStable StableArity.zero_option_fin_two)
    (w : C.H 2 (Fin 0 ⊕ Fin 2)) :
    (∑ i : Fin 2, (![2,-2] i : ℚ) • I.integrate 2 (Fin 0 ⊕ Fin 2)
      (StableArity.separating rightStable StableArity.zero_option_fin_two)
      (w * U.map (StrataModule.basis
        (rightColumn.separating (![leftColumn true, leftColumn false] i))))) = 0 := by
  apply A.certificate_separating_right_eq_zero B U F rightStable
    StableArity.zero_option_fin_two hAB w rightColumn
    ![leftColumn true, leftColumn false] rows ![2,-2] witness check
  have hz : ∀ i : Fin 2,
      B.map (StrataModule.basis (![leftColumn true, leftColumn false] i)) = 0 := by
    intro i
    apply C.eq_zero_of_dimension_lt 0 (Option (Fin 2))
      StableArity.zero_option_fin_two _ _ (B.map_basis_degree _)
    fin_cases i <;> decide
  intro row
  rw [RelationCertificate.interpret_apply, Fin.sum_univ_two, map_add, map_smul, map_smul,
    hz 0, hz 1, smul_zero, smul_zero, zero_add]

private def exceptionalSplits : Finset (SurfaceTarget.blowupTwo.Curve ×
    SurfaceTarget.blowupTwo.Curve) :=
  {(![0,0,0], ![1,1,0]), (![1,0,0], ![0,1,0]),
   (![0,1,0], ![1,0,0]), (![1,1,0], ![0,0,0])}

private theorem exceptionalSplits_eq :
    SurfaceTarget.blowupTwo.effective.splittings ![1,1,0] = exceptionalSplits := by
  rw [← SurfaceTarget.splittings_eq]
  decide

/-- Zero factors and both ordered exceptional splits survive. The equal
energy of E₁ and E₂ does not identify their component ancestor families. -/
example : SurfaceTarget.blowupTwo.effective.energy ![1,0,0] =
      SurfaceTarget.blowupTwo.effective.energy ![0,1,0] ∧
    (![1,0,0] : SurfaceTarget.blowupTwo.Curve) ≠ ![0,1,0] ∧
    exceptionalSplits.card = 4 := by decide

private theorem splitStable : StableArity 1 (Option (Fin 1)) := by
  norm_num only [StableArity, Fintype.card_option, Fintype.card_fin]

/-- The actual graph-to-GW ancestor chain retains all four full-class
splittings and arbitrary powers at retained markings and both node labels. -/
example {R V : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {C : StableCurveCohomology R} (I : StableCurveIntegration C)
    (P : PsiClasses C) (F : SeparatingPushforward C I)
    (A B : StrataRealization C 1 (Option (Fin 1)))
    (U : StrataRealization C 2 (Fin 1 ⊕ Fin 1))
    (hAB : A.SeparatingCompatible B U F splitStable splitStable)
    (hA : A.LegPsiCompatible P splitStable) (hB : B.LegPsiCompatible P splitStable)
    (hfundA : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Option (Fin 1)) splitStable)) = 1)
    (hfundB : B.map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Option (Fin 1)) splitStable)) = 1)
    (Omega : GromovWittenTheory R V SurfaceTarget.blowupTwo.Curve
      SurfaceTarget.blowupTwo.effective C)
    (a : Fin 1 ⊕ Fin 1 → V) (k l : Option (Fin 1) → ℕ) :
    U.integrateAgainst I (StableArity.separating splitStable splitStable)
        (Omega.omega 2 (Fin 1 ⊕ Fin 1) (StableArity.separating splitStable splitStable)
          ![1,1,0] a)
        (StrataModule.separating
          (StrataModule.mulLegPsi k (StrataModule.basis
            (TautologicalStratum.fundamental 1 (Option (Fin 1)) splitStable)))
          (StrataModule.mulLegPsi l (StrataModule.basis
            (TautologicalStratum.fundamental 1 (Option (Fin 1)) splitStable)))) =
      ∑ split ∈ exceptionalSplits,
        Omega.pairing.pairContract
          (Omega.ancestorInvariant P I 1 (Option (Fin 1)) splitStable split.1 k)
          (Omega.ancestorInvariant P I 1 (Option (Fin 1)) splitStable split.2 l) a := by
  rw [A.integrateAgainst_separating_fundamental_gw B U P F splitStable splitStable
    hAB hA hB hfundA hfundB, exceptionalSplits_eq]

private noncomputable def rankTwoCohFT :
    CohFT ℚ (ℚ × ℚ) (constantStableCurveCohomology ℚ) :=
  (CommFrobeniusAlgebra.productAlgebra ℚ).toTopologicalCohFT.toConstantCohFT

/-- A genuine full rank-two CohFT yields a nonzero component contraction.
The constant model is used only for source ancestors, without a Gysin package. -/
example : rankTwoCohFT.pairing.pairContract
    (rankTwoCohFT.ancestor (constantStableCurveCohomology.psiClasses ℚ)
      (constantStableCurveCohomology.integration ℚ) 0 (Option (Fin 2))
      StableArity.zero_option_fin_two (fun _ ↦ 0))
    (rankTwoCohFT.ancestor (constantStableCurveCohomology.psiClasses ℚ)
      (constantStableCurveCohomology.integration ℚ) 0 (Option (Fin 2))
      StableArity.zero_option_fin_two (fun _ ↦ 0))
    (Sum.elim ![(2,3),(5,7)] ![(11,13),(17,19)]) = 7057 := by
  have ha : rankTwoCohFT.ancestor (constantStableCurveCohomology.psiClasses ℚ)
      (constantStableCurveCohomology.integration ℚ) 0 (Option (Fin 2))
      StableArity.zero_option_fin_two (fun _ ↦ 0) =
      rankTwoCohFT.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two := by
    ext a
    rw [CohFT.ancestor_zero_apply]
    rfl
  rw [ha]
  have hs := rankTwoCohFT.pairing.pairContractTarget_comp_map
    (rankTwoCohFT.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
    (rankTwoCohFT.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two)
    LinearMap.id LinearMap.id
  simp only [LinearMap.id_compMultilinearMap] at hs
  rw [← hs]
  rw [rankTwoCohFT.separating 0 0 (Fin 2) (Fin 2)]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    TensorProduct.map_id, LinearMap.id_apply, AlgHom.toLinearMap_apply]
  rw [Algebra.TensorProduct.includeLeft_apply, LinearMap.mul'_apply, mul_one]
  change (CommFrobeniusAlgebra.productAlgebra ℚ).correlator 0 (Fin 2 ⊕ Fin 2)
    (Sum.elim ![(2,3),(5,7)] ![(11,13),(17,19)]) = 7057
  rw [CommFrobeniusAlgebra.correlator_apply, pow_zero, mul_one,
    Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two]
  change CommFrobeniusAlgebra.productCounit ℚ
    (((2,3) : ℚ × ℚ) * (5,7) * ((11,13) * (17,19))) = 7057
  norm_num only [CommFrobeniusAlgebra.productCounit_apply, Prod.fst_mul, Prod.snd_mul]

/-- The scalarization interface accepts a linear functional that cannot
be an algebra homomorphism: it fails to preserve this product. -/
example : CommFrobeniusAlgebra.productCounit ℚ ((1,0) * (0,1)) ≠
    CommFrobeniusAlgebra.productCounit ℚ (1,0) *
      CommFrobeniusAlgebra.productCounit ℚ (0,1) := by
  norm_num only [CommFrobeniusAlgebra.productCounit_apply, Prod.fst_mul, Prod.snd_mul]

/-- A constant degree-zero target cannot satisfy proper separating Gysin
integration, preventing its use as a vacuous numerical boundary fixture. -/
example : ¬Nonempty (SeparatingPushforward (constantStableCurveCohomology ℚ)
    (constantStableCurveCohomology.integration ℚ)) := by
  rintro ⟨F⟩
  have he := F.integrate_push 0 0 (Fin 2) (Fin 2)
    StableArity.zero_option_fin_two StableArity.zero_option_fin_two (1 ⊗ₜ[ℚ] 1)
  rw [StableCurveIntegration.tensorIntegral_tmul] at he
  change (0 : ℚ) = 1 * 1 at he
  norm_num at he

end AxiomaticGWTest.Tautological.Separating
