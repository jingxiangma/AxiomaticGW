/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW
import Mathlib.Tactic.FinCases

/-!
# Tautological-strata regression tests

These examples test the public combinatorial and quotient APIs. They do not
claim a geometric construction of stable-curve cohomology.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest

open AxiomaticGW

namespace Tautological

/-- A one-loop graph used to check that an isomorphism may exchange the two
branches of an internal edge. -/
def loopGraph : StableGraphCode (Fin 1) where
  vertexCount := 1
  edgeCount := 1
  vertexCount_pos := by omega
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
    have hlegs :
        Fintype.card {s : Fin 1 // (0 : Fin 1) = 0} = 1 := by
      calc
        Fintype.card {s : Fin 1 // (0 : Fin 1) = 0} =
            Fintype.card (Fin 1) :=
          Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl)
        _ = 1 := Fintype.card_fin 1
    have hflags :
        Fintype.card {p : Fin 1 × Fin 2 // (0 : Fin 1) = 0} = 2 := by
      calc
        Fintype.card {p : Fin 1 × Fin 2 // (0 : Fin 1) = 0} =
            Fintype.card (Fin 1 × Fin 2) :=
          Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl)
        _ = Fintype.card (Fin 1) * Fintype.card (Fin 2) :=
          Fintype.card_prod (Fin 1) (Fin 2)
        _ = 2 := by norm_num only [Fintype.card_fin]
    change 3 ≤ 2 * 0 +
      Fintype.card {s : Fin 1 // (0 : Fin 1) = 0} +
      Fintype.card {p : Fin 1 × Fin 2 // (0 : Fin 1) = 0}
    rw [hlegs, hflags]

def loopLeft : DecoratedStableGraph (Fin 1) where
  graph := loopGraph
  kappaPower := 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ i ↦ if i = 0 then 1 else 0

def loopRight : DecoratedStableGraph (Fin 1) where
  graph := loopGraph
  kappaPower := 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ i ↦ if i = 1 then 1 else 0

def loopBranchSwap : DecoratedStableGraph.Iso loopLeft loopRight where
  graphIso := {
    vertexEquiv := Equiv.refl _
    edgeEquiv := Equiv.refl _
    branchEquiv := fun _ ↦ Equiv.swap 0 1
    legVertex_comm := by intros; rfl
    endpoint_comm := by intros; rfl
    genus_comm := by intros; rfl }
  kappaPower_comm := by intros; rfl
  legPsiPower_comm := by intros; rfl
  halfEdgePsiPower_comm := by
    intro edge i
    fin_cases edge
    fin_cases i <;> rfl

theorem loopGraph_totalGenus : loopGraph.totalGenus = 1 := by
  unfold StableGraphCode.totalGenus StableGraphCode.firstBetti loopGraph
  norm_num only [Finset.sum_const_zero, Fintype.card_fin]

/-- Branch exchange does not create a second tautological basis stratum. -/
example :
    TautologicalStratum.mk loopLeft (by
      change loopGraph.totalGenus = 1
      exact loopGraph_totalGenus) =
      TautologicalStratum.mk loopRight (by
        change loopGraph.totalGenus = 1
        exact loopGraph_totalGenus) := by
  apply TautologicalStratum.mk_eq_mk
  exact ⟨loopBranchSwap⟩

/-- The one-vertex fundamental stratum is in codimension zero. -/
example :
    (TautologicalStratum.fundamental 0 (Fin 4)
      PointTarget.genusZero_four_stable).codimension = 0 := by
  exact TautologicalStratum.fundamental_codimension 0 (Fin 4)
    PointTarget.genusZero_four_stable

/-- Getzler's coefficient vector is the exact seven-term vector from the
relation. -/
example :
    GetzlerStratum.coefficient .delta22 = 12 ∧
      GetzlerStratum.coefficient .delta23 = -4 ∧
      GetzlerStratum.coefficient .delta24 = -2 ∧
      GetzlerStratum.coefficient .delta34 = 6 ∧
      GetzlerStratum.coefficient .delta03 = 1 ∧
      GetzlerStratum.coefficient .delta04 = 1 ∧
      GetzlerStratum.coefficient .deltaBeta = -2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An encoding keeps Getzler's relation in codimension two and kills it only
in the quotient where it is explicitly supplied as a relation. -/
example (E : GetzlerStrataEncoding) :
    E.relation ∈ StrataModule.degree 2 ∧
      StrataModule.quotientMk E.knownRelations E.relation = 0 := by
  exact ⟨E.relation_mem_degree, E.relation_eq_zero⟩

example : Fintype.card GetzlerStratum = 7 :=
  getzlerStratum_card

/-- A geometric Getzler package gives a quotient factor only after the cycle
compatibility equations are supplied. -/
example {R : Type*} [CommRing R] [Algebra ℚ R]
    {C : StableCurveCohomology R}
    (E : GetzlerStrataEncoding) (A : StrataRealization C 1 (Fin 4))
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, A.map (E.cycle x) = G.cycle x) :
    E.knownRelations ≤ A.kernel := by
  exact E.knownRelations_le_realization_kernel A G hcycle

/-- The executable genus-zero formula reproduces the first multinomial
values. -/
example :
    PointTarget.genusZeroPsiValue 3 (fun _ ↦ 0) = 1 ∧
      PointTarget.genusZeroPsiValue 4
        (PointTarget.singlePsiExponent 0 1) = 1 ∧
      PointTarget.genusZeroPsiValue 5
        PointTarget.zeroFiveTwoPsiExponent = 2 := by
  exact ⟨PointTarget.genusZeroPsiValue_zero_three,
    PointTarget.genusZeroPsiValue_zero_four,
    PointTarget.genusZeroPsiValue_zero_five_two_psi⟩

end Tautological

end AxiomaticGWTest
