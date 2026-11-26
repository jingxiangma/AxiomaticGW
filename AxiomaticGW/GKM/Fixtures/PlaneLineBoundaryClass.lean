/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneLineBoundaryData
public import AxiomaticGW.Tautological.RationalPsiRelation
public import AxiomaticGW.Tautological.StrataOperation
public import AxiomaticGW.Tautological.WDVVForgetful
public import Mathlib.Tactic.Ring

/-!
# A degree-one plane fixed-locus class before integration

The two distinct fixed-point lifts of the point and the two toric hyperplane
lifts leave the partition 12|34. Stabilizing the unmarked degree-one bridge
joins its two contracted endpoints. Inserting a fifth marking with unit
restriction gives two placements and two opposite flag-psi corrections.
The two original four-point psi relations attached at the node identify both
corrections with the same three-vertex stratum. Their poles cancel there.
-/

@[expose] public section
namespace AxiomaticGW.GKM.PlaneLineBoundaryClass
open EquivariantCoefficients PlaneLineBoundaryData
noncomputable section

/-- After contracting the moving line, its endpoint flags form the two branches of one node. -/
def incidence {n : ℕ} (leg : Fin n → Fin 2) : StableGraphCode.Candidate (Fin n) 2 1 :=
  { legVertex := leg, endpoint := ![![0, 1]], genus := ![0, 0] }

/-- The flag powers survive as cotangent powers of the two node branches. -/
def bridge {n : ℕ} (leg : Fin n → Fin 2) (valid : (incidence leg).Valid 0)
    (flags : Fin 2 → ℕ) : DecoratedStableGraph (Fin n) where
  graph := (incidence leg).toGraph valid
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := ![flags]

/-- Stabilized four-point locus in the independently ordered fixed-point lifts. -/
def baseGraph := bridge baseLeg (by decide +kernel) ![0, 0]

/-- The two five-point loci and the node cotangent powers of their four-point components. -/
def unitGraph (i : Fin 2) (power : ℕ) : DecoratedStableGraph (Fin 5) :=
  Fin.cases (bridge leftLeg (by decide +kernel) ![power, 0])
    (fun _ ↦ bridge rightLeg (by decide +kernel) ![0, power]) i

theorem unitGraph_genus (i : Fin 2) (power : ℕ) : (unitGraph i power).graph.totalGenus = 0 := by
  fin_cases i <;> rfl

/-- A particular five-point raw graph with the indicated power at its moving-side flag. -/
def unitStratum (i : Fin 2) (power : ℕ) : TautologicalStratum 0 (Fin 5) :=
  .mk _ (unitGraph_genus i power)

/-- The stabilized four-point graph is exactly the ordered raw WDVV boundary column 12|34. -/
theorem base_column : TautologicalStratum.mk baseGraph (by decide +kernel) = WDVV.columns 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic? _ _ (by decide +kernel)

/-- The genus-zero expansion starts with the inverse tangent Euler and flag weights. -/
def weight : Coefficient :=
  edge * tangent * insertions / (automorphism * (eulerLeft * eulerRight) * (flagLeft * flagRight))

theorem weight_one : weight = 1 := by
  have hc : x ^ 2 * y ^ 2 - x * y ^ 3 ≠ 0 := by
    rw [show x ^ 2 * y ^ 2 - x * y ^ 3 = x * y ^ 2 * (x - y) by ring]
    exact mul_ne_zero (mul_ne_zero x_ne_zero (pow_ne_zero _ y_ne_zero)) x_sub_y_ne_zero
  have hr : -x * y + y ^ 2 ≠ 0 := by
    rw [show -x * y + y ^ 2 = y * (y - x) by ring]
    exact mul_ne_zero y_ne_zero y_sub_x_ne_zero
  unfold weight edge tangent insertions automorphism eulerLeft eulerRight flagLeft flagRight
  apply (div_eq_iff (by
    exact mul_ne_zero (mul_ne_zero one_ne_zero (mul_ne_zero (mul_ne_zero x_ne_zero y_ne_zero) hr))
      (mul_ne_zero y_ne_zero (neg_ne_zero.mpr y_ne_zero)))).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hc]
  ring

/-- The base and both extra flag coefficients agree with the independent expansion. -/
theorem incoming : baseClaim = weight ∧ psiLeft = weight / flagLeft ∧
    psiRight = weight / flagRight := by rw [weight_one]; exact ⟨rfl, rfl, rfl⟩

theorem base_regular : Specializes weight 1 := by
  simpa only [map_one] using specializes_of_eq_polynomial (f := weight) 1
    (by simpa only [map_one] using weight_one)

/-- Attach the unchanged three-point component at the distinguished cotangent marking.
The old two labels of the other endpoint and the appended unit retain their order. -/
def attach (i : Fin 2) : StrataOperation 0 (Fin 4) 0 (Fin 5) :=
  let fixed := DecoratedStableGraph.oneVertex 0 (Fin 3) StableArity.zero_fin_three 0 (fun _ ↦ 0)
  let joined := (.input : StrataOperation 0 (Fin 4) 0 (Fin 4)).join fixed
    (DecoratedStableGraph.oneVertex_totalGenus _ _ _ _ _) StableArity.zero_fin_three 0 2
  let left : Fin 5 ≃ Fin 5 :=
    ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide +kernel, by decide +kernel⟩
  let right : Fin 5 ≃ Fin 5 :=
    ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide +kernel, by decide +kernel⟩
  joined.relabel (Fin.cases left (fun _ ↦ right) i)

/-- The two cotangent boundary refinements have a central rational component carrying the unit. -/
def centralGraph : DecoratedStableGraph (Fin 5) where
  graph :=
    ({ legVertex := ![0, 0, 2, 2, 1]
       endpoint := ![![0, 1], ![1, 2]]
       genus := ![0, 0, 0] } : StableGraphCode.Candidate (Fin 5) 3 2).toGraph
      (g := 0) (by decide +kernel)
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ _ ↦ 0

def central : TautologicalStratum 0 (Fin 5) := .mk centralGraph (by decide +kernel)

/-- Both original leading psi graphs and both boundary graphs match the held labelled loci. -/
theorem flag_bindings (i : Fin 2) :
    ((attach i).graph (RationalPsiRelation.graph 1 0)).isomorphic? (unitGraph i 1) = true ∧
    ((attach i).graph (RationalPsiRelation.graph 1 1)).isomorphic? centralGraph = true := by
  fin_cases i <;> decide +kernel

/-- Each pole's graph minus the same refinement is the image of the original four-marked
rational psi relation under the explicit attachment, with no target relation assumed. -/
theorem attached_relation (i : Fin 2) :
    (attach i).map (RelationCertificate.interpret (RationalPsiRelation.columns 1)
      (RationalPsiRelation.coordinates 1)) = StrataModule.basis (unitStratum i 1) -
      StrataModule.basis central := by
  have h (j : Fin 2) := (attach i).map_basis (RationalPsiRelation.graph 1 j)
    (RationalPsiRelation.graph_totalGenus 1 j)
  rw [RelationCertificate.interpret_apply]
  change (attach i).map (∑ j : Fin 2, _ • StrataModule.basis _) = _
  rw [Fin.sum_univ_two]
  change (attach i).map ((1 : ℚ) • StrataModule.basis _ + (-1 : ℚ) • StrataModule.basis _) = _
  simp only [one_smul, neg_one_smul, map_add, map_neg, RationalPsiRelation.columns]
  rw [h 0, h 1]
  have e0 := TautologicalStratum.mk_eq_mk_of_isomorphic?
    ((attach i).graph_totalGenus _ (RationalPsiRelation.graph_totalGenus 1 0)) (unitGraph_genus i 1)
    (flag_bindings i).1
  have e1 := TautologicalStratum.mk_eq_mk_of_isomorphic?
    ((attach i).graph_totalGenus _ (RationalPsiRelation.graph_totalGenus 1 1))
    (show centralGraph.graph.totalGenus = 0 by decide +kernel) (flag_bindings i).2
  exact (congrArg₂ (fun a b ↦ StrataModule.basis a + -StrataModule.basis b) e0 e1).trans
    (sub_eq_add_neg _ _).symm

/-- Pole-free four- and five-point rational representatives. -/
def baseClass : StrataModule 0 (Fin 4) := StrataModule.basis (WDVV.columns 0)

def unitClass : StrataModule 0 (Fin 5) :=
  StrataModule.basis (unitStratum 0 0) + StrataModule.basis (unitStratum 1 0)

/-- Pair the whole five-point equivariant packet against a rational linear functional. -/
def unitPairing (ev : StrataModule 0 (Fin 5) →ₗ[ℚ] ℚ) : Coefficient :=
  weight * (ev unitClass : Coefficient) +
    psiLeft * (ev (StrataModule.basis (unitStratum 0 1)) : Coefficient) +
    psiRight * (ev (StrataModule.basis (unitStratum 1 1)) : Coefficient)

/-- The full class has a regular ordinary specialization after the two original
four-point cotangent relations have been attached at their correct flags. -/
theorem unit_regular (ev : StrataModule 0 (Fin 5) →ₗ[ℚ] ℚ)
    (h : ∀ i, ev ((attach i).map (RelationCertificate.interpret
      (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1))) = 0) :
    Specializes (unitPairing ev) (ev unitClass) := by
  have he (i : Fin 2) : ev (StrataModule.basis (unitStratum i 1)) =
      ev (StrataModule.basis central) := by
    have hi := h i
    rw [attached_relation, map_sub, sub_eq_zero] at hi
    exact hi
  have hu : unitPairing ev = (ev unitClass : Coefficient) := by
    rw [unitPairing, weight_one, one_mul, he 0, he 1]
    unfold psiLeft psiRight
    rw [div_neg]
    ring
  simpa only [atZero, MvPolynomial.eval₂Hom_C, RingHom.id_apply] using
    specializes_of_eq_polynomial (f := unitPairing ev) (MvPolynomial.C (ev unitClass))
      (by rw [embed_C, hu])

/-- Interpret the appended external label as the new marking of the universal curve. -/
def labels : Fin 5 ≃ Option (Fin 4) := (ExtraMarkings.finEquiv 1 4).symm

private def placements := (WDVV.expression 0).addMarkings 1

/-- The two surviving fixed loci realize exactly the two terms of the forgetful pullback. -/
theorem marked_column : StrataModule.relabel labels unitClass =
    (((WDVV.expression 0).addMarkings 1).map fun z ↦ StrataModule.basis z.stratum).sum := by
  have h0 := TautologicalStratum.mk_eq_mk_of_isomorphic?
    (G := (unitGraph 0 0).relabel labels) (unitGraph_genus 0 0)
    (placements[0]'(by decide)).graph_totalGenus (by decide +kernel)
  have h1 := TautologicalStratum.mk_eq_mk_of_isomorphic?
    (G := (unitGraph 1 0).relabel labels) (unitGraph_genus 1 0)
    (placements[1]'(by decide)).graph_totalGenus (by decide +kernel)
  rw [unitClass, map_add, StrataModule.relabel_basis, StrataModule.relabel_basis]
  change StrataModule.basis (.mk _ _) + StrataModule.basis (.mk _ _) = _
  rw [h0, h1]
  change StrataModule.basis (placements[0]'(by decide)).stratum +
    StrataModule.basis (placements[1]'(by decide)).stratum =
    _ + (StrataModule.basis (placements[1]'(by decide)).stratum + 0)
  exact congrArg (fun z ↦ StrataModule.basis (placements[0]'(by decide)).stratum + z)
    (add_zero _).symm

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Gluing the original four-point cotangent relation proves the equality of the
two realized pole graphs with the common refinement. The source relation follows
from `RationalPsiRelation.realized_coordinates` using the primitive psi formula. -/
theorem map_flag (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (P : PsiClasses C) (i : Fin 2)
    (hc : (attach i).Compatible A F P WDVV.stableArity)
    (hpsi : (A 0 (Fin 4)).map (RelationCertificate.interpret
      (RationalPsiRelation.columns 1) (RationalPsiRelation.coordinates 1)) = 0) :
    (A 0 (Fin 5)).map (StrataModule.basis (unitStratum i 1)) =
      (A 0 (Fin 5)).map (StrataModule.basis central) := by
  have h := (attach i).map_vanishes A F P WDVV.stableArity hc _ hpsi
  rwa [attached_relation, map_sub, sub_eq_zero] at h

/-- On these two requests the ordinary class with the unit inserted is the
forgetful pullback, under the primitive universal-curve and gluing realization laws. -/
theorem map_unit (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hbase : (WDVV.expression 0).Compatible A F N)
    (hup : ∀ z ∈ (WDVV.expression 0).addMarkings 1, z.Compatible A F N) :
    (A 0 (Option (Fin 4))).map (StrataModule.relabel labels unitClass) =
      C.forget 0 (Fin 4) WDVV.stableArity ((A 0 (Fin 4)).map baseClass) := by
  rw [marked_column, map_list_sum, List.map_map]
  exact (WDVV.expression 0).sum_map_stratum_addMarkings A F N H 1 hbase hup

end
end AxiomaticGW.GKM.PlaneLineBoundaryClass
