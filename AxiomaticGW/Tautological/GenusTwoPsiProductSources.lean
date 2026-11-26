/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusTwoPsiProduct

/-!
# Source geometry for the two-marked cotangent product

The three boundary rows are actual separating images of already held
genus-two and genus-one component rows. No target boundary-row vanishing
or final cotangent identity is supplied as a geometric hypothesis.
-/

@[expose] public section

namespace AxiomaticGW.GenusTwoPsiProduct
open RelationCertificate
universe u

/-- Indices of the existing original component rows, not numerical seeds. -/
abbrev sourceIndex : Fin 3 → Fin 16 := ![4, 5, 13]

/-- The existing component families for these three rows. -/
abbrev sourceFamily (b : Fin 3) : Fin 7 := BelorousskiPandharipande.sourceFamily (sourceIndex b)

/-- The three boundary rows in the thirteen-row target frame. -/
def boundaryRow : Fin 3 → Fin 13 := ![10, 11, 12]

/-- Original node and marking powers are retained in these destinations. -/
def destinations : (b : Fin 3) →
    Fin (BelorousskiPandharipande.sourceSize (sourceFamily b)) → Fin 38 :=
  Fin.cases ![7, 8, 19, 29] (Fin.cases ![23, 24, 33]
    (Fin.cases ![9, 10, 11, 12, 20, 21, 19, 22, 36] (fun i ↦ Fin.elim0 i)))

/-- Actual attachment to a rational or elliptic fundamental component. -/
noncomputable def sourceMap : (b : Fin 3) →
    StrataModule (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b))) →ₗ[ℚ] StrataModule 2 (Fin 2) :=
  Fin.cases (BelorousskiPandharipande.attach (g := 2) (h := 0) (m := 0) (n := 2) 0
      (by norm_num [StableArity]))
    (Fin.cases (BelorousskiPandharipande.attach (g := 1) (h := 1) (m := 0) (n := 2) 0
      (by norm_num [StableArity]))
    (Fin.cases (BelorousskiPandharipande.attach (g := 1) (h := 1) (m := 2) (n := 0) 2
      (by norm_num [StableArity])) (fun i ↦ Fin.elim0 i)))

/-- The elementary decorated graph operations underlying the three linear maps. -/
noncomputable def sourceImage : (b : Fin 3) →
    TautologicalStratum (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b))) →
        TautologicalStratum 2 (Fin 2) :=
  Fin.cases (fun x ↦ ((x.relabel (finSuccEquiv' (0 : Fin 1))).separating
      (TautologicalStratum.fundamental 0 (Option (Fin 2)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)
    (Fin.cases (fun x ↦ ((x.relabel (finSuccEquiv' (0 : Fin 1))).separating
      (TautologicalStratum.fundamental 1 (Option (Fin 2)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv)
    (Fin.cases (fun x ↦ ((x.relabel (finSuccEquiv' (2 : Fin 3))).separating
      (TautologicalStratum.fundamental 1 (Option (Fin 0)) (by norm_num [StableArity]))).relabel
        finSumFinEquiv) (fun i ↦ Fin.elim0 i)))

/-- Linear attachment and the actual operation agree on every basis stratum. -/
theorem sourceMap_basis (b : Fin 3)
    (x : TautologicalStratum (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))) :
    sourceMap b (StrataModule.basis x) = StrataModule.basis (sourceImage b x) := by
  fin_cases b
  · exact BelorousskiPandharipande.attach_basis (g := 2) (h := 0) (m := 0) (n := 2) 0 _ x
  · exact BelorousskiPandharipande.attach_basis (g := 1) (h := 1) (m := 0) (n := 2) 0 _ x
  · exact BelorousskiPandharipande.attach_basis (g := 1) (h := 1) (m := 2) (n := 0) 2 _ x

/-- Incidence and all branch decorations determine the held destinations. -/
theorem sourceImage_columns : ∀ b i,
    sourceImage b (BelorousskiPandharipande.sourceColumns (sourceFamily b) i) =
      columns (destinations b i) := by
  simp only [sourceImage, BelorousskiPandharipande.sourceColumns,
    BelorousskiPandharipande.sourceGraph, columns, graph,
    BelorousskiPandharipande.tableGraph, GenusOnePsi.graph,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide +kernel

/-- Every source column has its checked semantic image under the linear map. -/
theorem sourceMap_columns (b : Fin 3)
    (i : Fin (BelorousskiPandharipande.sourceSize (sourceFamily b))) :
    sourceMap b (StrataModule.basis (BelorousskiPandharipande.sourceColumns (sourceFamily b) i)) =
      StrataModule.basis (columns (destinations b i)) := by
  rw [sourceMap_basis, sourceImage_columns]

/-- Exact source coefficients give the three held boundary rows. -/
theorem source_coordinates : ∀ b,
    rows (boundaryRow b) = combination (fun i ↦ Pi.single (destinations b i) 1)
      ⟨BelorousskiPandharipande.sourceRow (sourceIndex b)⟩ := by decide +kernel

/-- This is an equality of actual formal pushforwards, not a numerical check. -/
theorem sourceMap_row (b : Fin 3) :
    sourceMap b (BelorousskiPandharipande.sourceExpression (sourceIndex b)) =
      interpret columns (rows (boundaryRow b)) := by
  rw [BelorousskiPandharipande.sourceExpression, interpret_apply, map_sum,
    source_coordinates, interpret_combination]
  simp only [map_smul, sourceMap_columns, interpret,
    Fintype.linearCombination_apply_single, one_smul]

attribute [local instance] strataRealizationModule

/-- Only the primitive relabelling and separating laws used by these attachments. -/
def SourceCompatible {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) : Fin 3 → Prop :=
  Fin.cases (BelorousskiPandharipande.AttachCompatible Z F (g := 2) (h := 0) (m := 0) (n := 2) 0
      (BelorousskiPandharipande.sourceStable 2) (by norm_num [StableArity]))
    (Fin.cases (BelorousskiPandharipande.AttachCompatible Z F (g := 1) (h := 1) (m := 0) (n := 2) 0
      (BelorousskiPandharipande.sourceStable 3) (by norm_num [StableArity]))
    (Fin.cases (BelorousskiPandharipande.AttachCompatible Z F (g := 1) (h := 1) (m := 2) (n := 0) 2
      (BelorousskiPandharipande.sourceStable 6) (by norm_num [StableArity])) (fun i ↦ Fin.elim0 i)))

/-- Original source vanishing propagates through the actual graph maps. -/
theorem boundary_rows_vanish {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (hc : ∀ b, SourceCompatible Z F b)
    (hsource : ∀ b, (Z (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (sourceIndex b)) = 0) (b : Fin 3) :
    (Z 2 (Fin 2)).map (interpret columns (rows (boundaryRow b))) = 0 := by
  rw [← sourceMap_row]
  fin_cases b
  · exact BelorousskiPandharipande.attach_vanishes Z F 0 (BelorousskiPandharipande.sourceStable 2)
      _ (hc 0) _ (hsource 0)
  · exact BelorousskiPandharipande.attach_vanishes Z F 0 (BelorousskiPandharipande.sourceStable 3)
      _ (hc 1) _ (hsource 1)
  · exact BelorousskiPandharipande.attach_vanishes Z F 2 (BelorousskiPandharipande.sourceStable 6)
      _ (hc 2) _ (hsource 2)

/-- All thirteen inputs follow from ten original interior rows and three component rows. -/
theorem rows_vanish_from_generators {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (hc : ∀ b, SourceCompatible Z F b)
    (hsource : ∀ b, (Z (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (sourceIndex b)) = 0)
    (hinterior : ∀ i : Fin 10,
      (Z 2 (Fin 2)).map (interpret columns (rows (i.castLE (by decide)))) = 0)
    (i : Fin 13) : (Z 2 (Fin 2)).map (interpret columns (rows i)) = 0 := by
  refine Fin.addCases (m := 10) (n := 3) (fun j ↦ hinterior j) (fun j ↦ ?_) i
  have hj : j.natAdd 10 = boundaryRow j := by fin_cases j <;> rfl
  rw [hj]
  exact boundary_rows_vanish Z F hc hsource j

/-- The complete class identity follows from the original generators and primitive geometry. -/
theorem realized_psi_product_from_generators {R : Type u} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (p : Exchange) (hp : AcceptsExchange p)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C)
    (hc : ∀ b, SourceCompatible Z F b)
    (hsource : ∀ b, (Z (BelorousskiPandharipande.sourceGenus (sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (sourceIndex b)) = 0)
    (hinterior : ∀ i : Fin 10,
      (Z 2 (Fin 2)).map (interpret columns (rows (i.castLE (by decide)))) = 0)
    (hpsi : (Z 2 (Fin 2)).LegPsiCompatible P stableArity)
    (hfund : (Z 2 (Fin 2)).map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 2) stableArity)) = 1) :
    P.psi 2 (Fin 2) stableArity 0 * P.psi 2 (Fin 2) stableArity 1 =
      (Z 2 (Fin 2)).map (interpret columns boundary) := by
  have he := evaluated_relation p hp (Z 2 (Fin 2)).map
    (rows_vanish_from_generators Z F hc hsource hinterior)
  rw [psi_product_column, StrataRealization.map_addLegPsi _ P _ hpsi, hfund, one_mul] at he
  simpa only [PsiClasses.monomial, Fin.prod_univ_two, pow_one] using he

end AxiomaticGW.GenusTwoPsiProduct
