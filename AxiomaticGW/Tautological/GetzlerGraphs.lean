/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.Getzler
public import AxiomaticGW.Tautological.GraphEnumeration
public import AxiomaticGW.Tautological.Relabel
public import AxiomaticGW.Tautological.RelationCertificate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The seven normalized Getzler cycles as marked raw graphs

The fixed frame contains 33 distinct undecorated labelled graphs. The four
elliptic tree orbits have sizes 3, 12, 6, 4; the loop-and-tail orbits have
sizes 4, 1; the two-parallel-edge orbit has size 3. External labels are 0--3.

Getzler's orbifold stratum class is the raw gluing pushforward divided by
its label-fixing graph automorphism order (Proposition 1.6). This order is
one for the trees and two for the loop and parallel-edge graphs. It is
separate from the generic stabilizer of a point of the moduli stack: the
elliptic component stack already accounts for that stabilizer. In particular
no additional division by two occurs for delta23 or delta24.

Sources: Getzler, arXiv:alg-geom/9612004v2, Section 1, pages 3--6 and
Theorem 1.8. Graph normalization is explicit; geometric relation validity
remains the existing GetzlerRelationGeometry input.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

open scoped BigOperators

/-- The full stable four-marked genus-one target. -/
theorem stableArity : StableArity 1 (Fin 4) := by norm_num [StableArity]

/-- Tree columns: vertex zero is elliptic. The first three have two rational
tails; the others are chains with the rational tail at vertex two. -/
def treeCandidate (i : Fin 25) : StableGraphCode.Candidate (Fin 4) 3 2 where
  legVertex := ![
    ![1, 1, 2, 2],
    ![1, 2, 1, 2],
    ![1, 2, 2, 1],
    ![2, 2, 1, 0],
    ![2, 2, 0, 1],
    ![2, 1, 2, 0],
    ![2, 0, 2, 1],
    ![2, 1, 0, 2],
    ![2, 0, 1, 2],
    ![1, 2, 2, 0],
    ![0, 2, 2, 1],
    ![1, 2, 0, 2],
    ![0, 2, 1, 2],
    ![1, 0, 2, 2],
    ![0, 1, 2, 2],
    ![2, 2, 1, 1],
    ![2, 1, 2, 1],
    ![2, 1, 1, 2],
    ![1, 2, 2, 1],
    ![1, 2, 1, 2],
    ![1, 1, 2, 2],
    ![1, 2, 2, 2],
    ![2, 1, 2, 2],
    ![2, 2, 1, 2],
    ![2, 2, 2, 1]] i
  endpoint := if i.val < 3 then ![![0, 1], ![0, 2]] else ![![0, 1], ![1, 2]]
  genus := ![1, 0, 0]

/-- Connectedness, vertex stability, and arithmetic genus of every tree. -/
theorem treeCandidate_valid (i : Fin 25) : (treeCandidate i).Valid 1 := by
  fin_cases i <;> decide

/-- Cyclic columns: four loop-and-triple-tail graphs, the loop-and-full-tail
graph, and the three unordered pair partitions on two parallel edges. -/
def cyclicCandidate (i : Fin 8) : StableGraphCode.Candidate (Fin 4) 2 2 where
  legVertex := ![
    ![0, 1, 1, 1],
    ![1, 0, 1, 1],
    ![1, 1, 0, 1],
    ![1, 1, 1, 0],
    ![1, 1, 1, 1],
    ![0, 0, 1, 1],
    ![0, 1, 0, 1],
    ![0, 1, 1, 0]] i
  endpoint := if i.val < 5 then ![![0, 0], ![0, 1]] else ![![0, 1], ![0, 1]]
  genus := ![0, 0]

/-- The cyclic columns are stable genus-one graphs, including the unmarked loop vertex. -/
theorem cyclicCandidate_valid (i : Fin 8) : (cyclicCandidate i).Valid 1 := by
  fin_cases i <;> decide

/-- Undecorated raw tree presentation. -/
def treeGraph (i : Fin 25) : DecoratedStableGraph (Fin 4) where
  graph := (treeCandidate i).toGraph (treeCandidate_valid i)
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ _ ↦ 0

/-- Undecorated raw cyclic presentation, retaining both node branches. -/
def cyclicGraph (i : Fin 8) : DecoratedStableGraph (Fin 4) where
  graph := (cyclicCandidate i).toGraph (cyclicCandidate_valid i)
  kappaPower := fun _ ↦ 0
  legPsiPower := fun _ ↦ 0
  halfEdgePsiPower := fun _ _ ↦ 0

/-- The fixed 33 raw graph presentations, ordered by named cycle. -/
def graph (i : Fin 33) : DecoratedStableGraph (Fin 4) :=
  if h : i.val < 25 then treeGraph ⟨i.val, h⟩
  else cyclicGraph ⟨i.val - 25, by omega⟩

/-- Every column belongs to genus one. -/
theorem graph_totalGenus (i : Fin 33) : (graph i).graph.totalGenus = 1 := by
  unfold graph
  split
  · exact (treeCandidate _).toGraph_totalGenus (treeCandidate_valid _)
  · exact (cyclicCandidate _).toGraph_totalGenus (cyclicCandidate_valid _)

/-- No psi or kappa decoration contributes: there are exactly two nodes. -/
theorem graph_codimension (i : Fin 33) : (graph i).codimension = 2 := by
  unfold graph
  split <;>
    simp only [treeGraph, cyclicGraph, DecoratedStableGraph.codimension,
      DecoratedStableGraph.kappaCodimension, DecoratedStableGraph.legPsiCodimension,
      DecoratedStableGraph.halfEdgePsiCodimension, Finsupp.sum_zero_index,
      Finset.sum_const_zero, Nat.add_zero]
    <;> rfl

/-- Raw graph classes, with external markings fixed under isomorphism. -/
def columns (i : Fin 33) : TautologicalStratum 1 (Fin 4) :=
  TautologicalStratum.mk (graph i) (graph_totalGenus i)

/-- The seven names partition the graph frame, with no orbit averaging. -/
def kind : Fin 33 → GetzlerStratum :=
  fun i ↦ if i.val < 3 then .delta22
    else if i.val < 15 then .delta23
    else if i.val < 21 then .delta24
    else if i.val < 25 then .delta34
    else if i.val < 29 then .delta03
    else if i.val < 30 then .delta04
    else .deltaBeta

/-- Graph automorphisms divide cyclic raw pushforwards by two. Tree source
stacks already retain the elliptic stabilizer, so their factor is one. -/
def normalization (i : Fin 33) : ℚ := if i.val < 25 then 1 else 1 / 2

set_option maxHeartbeats 2000000 in
-- The kernel enumerates the finite vertex, edge, and branch permutations of 33 graphs.
/-- The four tree families have order one; both cyclic families have order two. -/
theorem graph_automorphismCount (i : Fin 33) :
    (graph i).automorphismCount = if i.val < 25 then 1 else 2 := by
  have ht : ∀ i : Fin 25, (treeGraph i).automorphismCount = 1 := by decide
  have hc : ∀ i : Fin 8, (cyclicGraph i).automorphismCount = 2 := by decide
  unfold graph
  split
  · exact ht _
  · exact hc _

/-- The supplied factor is exactly the inverse of the computed graph order. -/
theorem normalization_eq_inverse_automorphism (i : Fin 33) :
    normalization i = ((graph i).automorphismCount : ℚ)⁻¹ := by
  rw [graph_automorphismCount]
  unfold normalization
  split <;> norm_num

/-- The frame has no duplicate labelled graph classes. -/
theorem columns_injective : Function.Injective columns := by
  have h : ∀ i j : Fin 33, (graph i).isomorphic? (graph j) = true ↔ i = j := by decide
  intro i j hij
  obtain ⟨e⟩ := Quotient.exact hij
  exact (h i j).mp ((DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mpr ⟨e⟩)

/-- The unique labelled members of one symmetric cycle. -/
def orbit (x : GetzlerStratum) : Finset (TautologicalStratum 1 (Fin 4)) :=
  (Finset.univ.filter (fun i ↦ kind i = x)).image columns

/-- Representatives of the seven marking orbits. -/
def representative : GetzlerStratum → Fin 33
  | .delta22 => 0
  | .delta23 => 3
  | .delta24 => 15
  | .delta34 => 21
  | .delta03 => 25
  | .delta04 => 29
  | .deltaBeta => 30

set_option maxHeartbeats 3000000 in
-- All 24 label permutations are checked against the explicit finite quotient columns.
/-- Each named list is exactly the full S4 orbit of its representative,
with quotient equality removing repeated presentations. -/
theorem orbit_eq_permutations (x : GetzlerStratum) :
    orbit x = Finset.univ.image (fun e : Equiv.Perm (Fin 4) ↦
      (columns (representative x)).relabel e) := by
  cases x <;> decide

/-- Marking orbit sizes in the order used in Getzler's relation. -/
def orbitSize : GetzlerStratum → ℕ
  | .delta22 => 3
  | .delta23 => 12
  | .delta24 => 6
  | .delta34 => 4
  | .delta03 => 4
  | .delta04 => 1
  | .deltaBeta => 3

/-- The sum runs once over each labelled stratum, rather than over 24 permutations. -/
theorem orbit_card (x : GetzlerStratum) : (orbit x).card = orbitSize x := by
  rw [orbit, Finset.card_image_of_injective _ columns_injective]
  cases x <;> decide

/-- Exact orbifold-to-raw coordinates of a named symmetric cycle. -/
def cycleCoordinates (x : GetzlerStratum) : RelationCertificate.Coordinates 33 :=
  fun i ↦ if kind i = x then normalization i else 0

/-- Explicit normalized symmetric cycle in the existing free strata module. -/
noncomputable def cycle (x : GetzlerStratum) : StrataModule 1 (Fin 4) :=
  RelationCertificate.interpret columns (cycleCoordinates x)

/-- Every normalized cycle remains homogeneous of codimension two. -/
theorem cycle_mem_degree (x : GetzlerStratum) : cycle x ∈ StrataModule.degree 2 :=
  RelationCertificate.interpret_mem_degree columns (graph_codimension) _

/-- Concrete instance of the pre-existing Getzler encoding contract. -/
noncomputable def encoding : GetzlerStrataEncoding where
  cycle := cycle
  cycle_degree := cycle_mem_degree

/-- The fixed Getzler row expressed in 33 raw labelled columns. -/
def row : RelationCertificate.Coordinates 33 :=
  fun i ↦ GetzlerStratum.coefficient (kind i) * normalization i

/-- Expanding the seven names produces the held raw row exactly. -/
theorem sum_cycleCoordinates :
    (∑ x, GetzlerStratum.coefficient x • cycleCoordinates x) = row := by
  funext i
  change (∑ x, GetzlerStratum.coefficient x * cycleCoordinates x i) = row i
  rw [Finset.sum_eq_single (kind i)]
  · simp only [cycleCoordinates, if_true, row]
  · intro x _ hx
    simp only [cycleCoordinates, Ne.symm hx, if_false, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The original encoding and the expanded graph relation agree in the free module. -/
theorem encoding_relation_eq : encoding.relation = RelationCertificate.interpret columns row := by
  calc
    encoding.relation = RelationCertificate.interpret columns
        (∑ x, GetzlerStratum.coefficient x • cycleCoordinates x) := by
      simp only [GetzlerStrataEncoding.relation, encoding, cycle, map_sum, map_smul]
    _ = RelationCertificate.interpret columns row := by rw [sum_cycleCoordinates]

/-- The original relation row remains separately fixed. -/
def rows : Fin 1 → RelationCertificate.Coordinates 33 := fun _ ↦ row

/-- Held consequence isolating delta23, specified independently of a witness. -/
def requested : RelationCertificate.Coordinates 33 := fun i ↦
  (match kind i with
    | .delta22 => -3
    | .delta23 => 1
    | .delta24 => 1 / 2
    | .delta34 => -3 / 2
    | .delta03 => -1 / 4
    | .delta04 => -1 / 4
    | .deltaBeta => 1 / 2) * normalization i

/-- A candidate's columns, raw factors, source row, and request must match this frame. -/
abbrev AcceptsExchange (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) : Prop :=
  RelationCertificate.AcceptsPresentation columns rows requested p

end AxiomaticGW.GetzlerGraphs
