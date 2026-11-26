/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW

set_option linter.privateModule false

/-!
# External psi operation regressions

The graph examples retain loop flips, internal decorations, and external
labels. A nonzero normalized constant realization exercises the actual
cohomology evaluator and a class-valued CohFT. It is an interface fixture,
not a geometric surface model or a positive-degree GW computation.
-/

namespace AxiomaticGWTest.Tautological.LegPsi

open AxiomaticGW

private def loopGraph : StableGraphCode (Fin 2) where
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
    exact Relation.ReflTransGen.refl
  stable := by
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    decide

private def loopDecoration (a b : ℕ) : DecoratedStableGraph (Fin 2) where
  graph := loopGraph
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ ↦ ![a,b]

/-- External powers leave a loop's two flips intact and retain each label. -/
example : ((loopDecoration 0 0).addLegPsi ![2,1]).automorphismCount = 2 ∧
    ((loopDecoration 0 0).addLegPsi ![2,1]).legPsiPower 0 = 2 ∧
    ((loopDecoration 0 0).addLegPsi ![2,1]).legPsiPower 1 = 1 := by decide

/-- An already broken loop flip remains broken; internal exponents stay put. -/
example : ((loopDecoration 0 1).addLegPsi ![2,1]).automorphismCount = 1 ∧
    ((loopDecoration 0 1).addLegPsi ![2,1]).halfEdgePsiPower ⟨0, by decide⟩ 1 = 1 := by decide

/-- The boundary edge and the three external powers contribute four in total. -/
example : ((loopDecoration 0 0).addLegPsi ![2,1]).codimension = 4 := by
  rw [DecoratedStableGraph.addLegPsi_codimension]
  decide

/-- Exchanging internal branches before external multiplication yields the
same quotient stratum, including unequal branch decorations. -/
example :
    (TautologicalStratum.mk (loopDecoration 0 1)
      (by decide : loopGraph.totalGenus = 1)).addLegPsi ![3,2] =
    (TautologicalStratum.mk (loopDecoration 1 0)
      (by decide : loopGraph.totalGenus = 1)).addLegPsi ![3,2] := by
  apply congrArg (fun x : TautologicalStratum 1 (Fin 2) ↦ x.addLegPsi ![3,2])
  apply TautologicalStratum.mk_eq_mk_of_isomorphic?
  decide

private theorem genusOne_two_stable : StableArity 1 (Fin 2) := by
  norm_num only [StableArity, Fintype.card_fin]

/-- Equal codimension does not identify psi at different external labels. -/
private theorem differentLabels :
    TautologicalStratum.oneVertex 1 (Fin 2) genusOne_two_stable 0 ![1,0] ≠
      TautologicalStratum.oneVertex 1 (Fin 2) genusOne_two_stable 0 ![0,1] := by
  intro h
  obtain ⟨e⟩ := Quotient.exact h
  have hc := e.legPsiPower_comm 0
  exact (by decide : (0 : ℕ) ≠ 1) hc

/-- Adding more powers cannot conceal a change of external label. -/
example :
    (TautologicalStratum.oneVertex 1 (Fin 2) genusOne_two_stable 0 ![1,0]).addLegPsi
      ![2,4] ≠
    (TautologicalStratum.oneVertex 1 (Fin 2) genusOne_two_stable 0 ![0,1]).addLegPsi
      ![2,4] := fun h ↦ differentLabels (TautologicalStratum.addLegPsi_injective _ h)

/-- The operation also handles empty external label sets. -/
example (x : TautologicalStratum 2 (Fin 0)) (k : Fin 0 → ℕ) : x.addLegPsi k = x := by
  have hk : k = 0 := funext fun s ↦ Fin.elim0 s
  rw [hk, TautologicalStratum.addLegPsi_zero]

/-- Rational coefficients and signs are retained on a genuine boundary graph. -/
example (k : Fin 2 → ℕ) :
    StrataModule.mulLegPsi k
      ((3 : ℚ) • StrataModule.basis
        (TautologicalStratum.mk (loopDecoration 0 0)
          (by decide : loopGraph.totalGenus = 1)) -
      (1 / 2 : ℚ) • StrataModule.basis
        (TautologicalStratum.mk (loopDecoration 0 1)
          (by decide : loopGraph.totalGenus = 1))) =
    (3 : ℚ) • StrataModule.basis
      ((TautologicalStratum.mk (loopDecoration 0 0)
        (by decide : loopGraph.totalGenus = 1)).addLegPsi k) -
    (1 / 2 : ℚ) • StrataModule.basis
      ((TautologicalStratum.mk (loopDecoration 0 1)
        (by decide : loopGraph.totalGenus = 1)).addLegPsi k) := by
  simp only [map_sub, map_smul, StrataModule.mulLegPsi_basis]

attribute [local instance] strataRealizationModule

/-- A normalized dimension-zero interface fixture. Every positive-degree
stratum maps to zero, while the fundamental stratum maps to one. -/
private noncomputable def zeroDimRealization :
    StrataRealization (constantStableCurveCohomology ℚ) 0 (Fin 3) where
  map := Finsupp.linearCombination ℚ (fun x ↦ if x.codimension = 0 then 1 else 0)
  map_basis_degree := by
    intro x
    change _ ∈ constantDegree ℚ x.codimension
    simp only [StrataModule.basis, Finsupp.linearCombination_single, one_smul]
    by_cases hx : x.codimension = 0
    · simp only [hx, ↓reduceIte, constantDegree, Submodule.mem_top]
    · simp only [hx, ↓reduceIte, constantDegree, Submodule.mem_bot]

private theorem zeroDim_compatible : zeroDimRealization.LegPsiCompatible
    (constantStableCurveCohomology.psiClasses ℚ) StableArity.zero_fin_three := by
  intro x s delta hs _
  have hle : delta s ≤ ∑ t, delta t :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ s)
  have hne : (x.addLegPsi delta).codimension ≠ 0 := by
    rw [TautologicalStratum.addLegPsi_codimension]
    omega
  change Finsupp.linearCombination ℚ _
    (StrataModule.basis (x.addLegPsi delta)) = _ * (0 : ℚ)
  simp only [StrataModule.basis, Finsupp.linearCombination_single,
    one_smul, hne, ↓reduceIte, mul_zero]

private theorem zeroDim_fundamental : zeroDimRealization.map
    (StrataModule.basis (TautologicalStratum.fundamental 0 (Fin 3)
      StableArity.zero_fin_three)) = 1 := by
  change Finsupp.linearCombination ℚ _ _ = 1
  simp only [StrataModule.basis, Finsupp.linearCombination_single, one_smul,
    TautologicalStratum.fundamental_codimension, ↓reduceIte]

/-- The normalized fixture has a nonzero actual integrated value. -/
example : zeroDimRealization.integrateAgainst
    (constantStableCurveCohomology.integration ℚ) StableArity.zero_fin_three 6
    (StrataModule.basis (TautologicalStratum.fundamental 0 (Fin 3)
      StableArity.zero_fin_three)) = 6 := by
  rw [StrataRealization.integrateAgainst_apply, zeroDim_fundamental, mul_one]
  rfl

/-- Positive external powers vanish by the actual cotangent classes of the
constant target, rather than an extra supplied output value. -/
example : zeroDimRealization.integrateAgainst
    (constantStableCurveCohomology.integration ℚ) StableArity.zero_fin_three 6
    (StrataModule.mulLegPsi ![2,0,0]
      (StrataModule.basis (TautologicalStratum.fundamental 0 (Fin 3)
        StableArity.zero_fin_three))) = 0 := by
  rw [StrataRealization.integrateAgainst_apply,
    zeroDimRealization.map_mulLegPsi _ _ zeroDim_compatible, zeroDim_fundamental, one_mul]
  have hpsi : (constantStableCurveCohomology.psiClasses ℚ).monomial
      0 (Fin 3) StableArity.zero_fin_three ![2,0,0] = 0 := by
    simp only [PsiClasses.monomial, constantStableCurveCohomology.psiClasses,
      Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, zero_pow (by decide : (2 : ℕ) ≠ 0), pow_zero,
      zero_mul, mul_one]
  rw [hpsi, mul_zero, map_zero]

/-- The evaluator consumes an existing full class-valued CohFT and agrees
with its ancestor correlator for arbitrary marking powers. -/
example (Omega : CohFT ℚ ℚ (constantStableCurveCohomology ℚ)) (a : Fin 3 → ℚ)
    (k : Fin 3 → ℕ) :
    zeroDimRealization.integrateAgainst (constantStableCurveCohomology.integration ℚ)
      StableArity.zero_fin_three (Omega.omega 0 (Fin 3) StableArity.zero_fin_three a)
      (StrataModule.mulLegPsi k
        (StrataModule.basis (TautologicalStratum.fundamental 0 (Fin 3)
          StableArity.zero_fin_three))) =
      Omega.ancestor (constantStableCurveCohomology.psiClasses ℚ)
        (constantStableCurveCohomology.integration ℚ)
        0 (Fin 3) StableArity.zero_fin_three k a :=
  zeroDimRealization.integrateAgainst_fundamental _ _ _
    zeroDim_compatible zeroDim_fundamental Omega a k

/-- An existing Frobenius algebra supplies the fixture's actual full CohFT. -/
private noncomputable def scalarCohFT :
    CohFT ℚ ℚ (constantStableCurveCohomology ℚ) :=
  (CommFrobeniusAlgebra.baseRing ℚ).toTopologicalCohFT.toConstantCohFT

/-- The class-valued ancestor comparison has a concrete nonzero instance. -/
example : zeroDimRealization.integrateAgainst
    (constantStableCurveCohomology.integration ℚ) StableArity.zero_fin_three
    (scalarCohFT.omega 0 (Fin 3) StableArity.zero_fin_three ![2,3,5])
    (StrataModule.mulLegPsi (fun _ ↦ 0)
      (StrataModule.basis (TautologicalStratum.fundamental 0 (Fin 3)
        StableArity.zero_fin_three))) = 30 := by
  rw [zeroDimRealization.integrateAgainst_fundamental _ _ _
    zeroDim_compatible zeroDim_fundamental]
  unfold scalarCohFT
  rw [TopologicalCohFT.toConstantCohFT_ancestor_zero_three]
  change (CommFrobeniusAlgebra.baseRing ℚ).correlator 0 (Fin 3) ![2,3,5] = 30
  rw [CommFrobeniusAlgebra.baseRing_correlator_apply]
  norm_num only [Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]

/-- This source relation is justified by dimension on the full stable locus. -/
private noncomputable def dimensionColumn : TautologicalStratum 0 (Fin 3) :=
  (TautologicalStratum.fundamental 0 (Fin 3) StableArity.zero_fin_three).addLegPsi ![1,0,0]

private theorem dimensionColumn_above :
    StableArity.dimension 0 (Fin 3) < dimensionColumn.codimension := by
  rw [StableArity.dimension_zero_fin_three]
  change 0 < (TautologicalStratum.addLegPsi _ ![1,0,0]).codimension
  rw [TautologicalStratum.addLegPsi_codimension, TautologicalStratum.fundamental_codimension]
  decide

private def dimensionRows : Fin 1 → RelationCertificate.Coordinates 1 := fun _ ↦ ![1]

private def dimensionCertificate : RelationCertificate.Certificate 1 := ⟨![2]⟩

private theorem dimensionCheck : RelationCertificate.check dimensionRows ![2]
    dimensionCertificate = true := by
  rw [RelationCertificate.check_eq_true_iff]
  funext i
  fin_cases i
  norm_num only [RelationCertificate.combination, dimensionRows, dimensionCertificate,
    Fin.sum_univ_one, Matrix.cons_val_fin_one]

/-- A fixed exact witness and original cohomological row vanishing prove
the multiplied integrated equation, with no assumed multiplied recurrence. -/
example : (∑ i : Fin 1, (![2] i : ℚ) •
    (constantStableCurveCohomology.integration ℚ).integrate 0 (Fin 3)
      StableArity.zero_fin_three
      ((6 : ℚ) * zeroDimRealization.map
        (StrataModule.basis (dimensionColumn.addLegPsi ![2,1,0])))) = 0 := by
  apply zeroDimRealization.certificate_mulLegPsi_eq_zero
    (constantStableCurveCohomology.psiClasses ℚ)
    (constantStableCurveCohomology.integration ℚ) StableArity.zero_fin_three
    zeroDim_compatible 6 ![2,1,0] (fun _ ↦ dimensionColumn)
    dimensionRows ![2] dimensionCertificate dimensionCheck
  intro row
  rw [RelationCertificate.interpret_apply, Fin.sum_univ_one]
  change zeroDimRealization.map (1 • StrataModule.basis dimensionColumn) = 0
  rw [one_smul]
  apply (zeroDimRealization.mem_kernel_iff _).mp
  exact zeroDimRealization.dimensionRelations_le_kernel StableArity.zero_fin_three
    (StrataModule.basis_mem_dimensionRelations dimensionColumn dimensionColumn_above)

end AxiomaticGWTest.Tautological.LegPsi
