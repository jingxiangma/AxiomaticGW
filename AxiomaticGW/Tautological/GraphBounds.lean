/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedStableGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Finsupp.Order

/-!
# Bounds for finite stable graph enumeration

The simple incidence graph forgets loops and parallel-edge multiplicities only
for connectivity and the spanning-tree bound. The stable graph presentation,
its branch data, and its decorations retain them. These bounds make the
bounded-degree strata syntax finite without adding hypotheses to its definition.
-/

@[expose] public section

open scoped BigOperators
namespace AxiomaticGW

namespace StableGraphCode

/-- Unoriented incidence relation, including loops. -/
def edgeRelation {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v) (x y : Fin v) : Prop :=
  ∃ edge, (endpoint edge 0 = x ∧ endpoint edge 1 = y) ∨
    (endpoint edge 1 = x ∧ endpoint edge 0 = y)

instance {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v) :
    DecidableRel (edgeRelation endpoint) := fun _ _ ↦
  inferInstanceAs (Decidable (∃ _edge, (_ : Prop) ∨ (_ : Prop)))

/-- Simple graph used solely to decide connectivity and bound vertices. -/
def incidenceGraph {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v) : SimpleGraph (Fin v) :=
  SimpleGraph.fromRel (edgeRelation endpoint)

instance {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v) :
    DecidableRel (incidenceGraph endpoint).Adj := inferInstanceAs
  (DecidableRel (SimpleGraph.fromRel (edgeRelation endpoint)).Adj)

/-- Removing loops and repeated adjacency preserves connectedness. -/
theorem reachable_iff {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v) (x y : Fin v) :
    (incidenceGraph endpoint).Reachable x y ↔
      Relation.ReflTransGen (edgeRelation endpoint) x y := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    apply Relation.ReflTransGen.mono ?_ x y h
    intro a b hab
    rcases hab.2 with h | h
    · exact h
    · rcases h with ⟨edge, h | h⟩
      · exact ⟨edge, Or.inr ⟨h.2, h.1⟩⟩
      · exact ⟨edge, Or.inl ⟨h.2, h.1⟩⟩
  · intro h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c hbc hstep ih =>
      by_cases h : b = c
      · subst c; exact ih
      · exact ih.trans (SimpleGraph.Adj.reachable ⟨h, Or.inl hstep⟩)

/-- A stable graph has a connected simple incidence graph. -/
theorem incidenceGraph_connected {S : Type} [Fintype S] (G : StableGraphCode S) :
    (incidenceGraph G.endpoint).Connected := by
  letI : Nonempty (Fin G.vertexCount) := ⟨⟨0, G.vertexCount_pos⟩⟩
  constructor
  intro v w
  exact (reachable_iff G.endpoint v w).2 (G.connected v w)

/-- A spanning tree bounds vertices by internal edges plus one. -/
theorem vertexCount_le_edgeCount_add_one {S : Type} [Fintype S] (G : StableGraphCode S) :
    G.vertexCount ≤ G.edgeCount + 1 := by
  classical
  let graph := incidenceGraph G.endpoint
  have hcard : Nat.card (Fin G.vertexCount) ≤ Nat.card graph.edgeSet + 1 :=
    (incidenceGraph_connected G).card_vert_le_card_edgeSet_add_one
  have hsubset : graph.edgeSet ⊆ Set.range
      (fun edge : Fin G.edgeCount ↦ s(G.endpoint edge 0, G.endpoint edge 1)) := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ x y =>
      have hxy : graph.Adj x y := (SimpleGraph.mem_edgeSet _).mp hedge
      rcases hxy.2 with h | h
      · rcases h with ⟨e, he | he⟩
        · exact ⟨e, by dsimp only; rw [he.1, he.2]⟩
        · exact ⟨e, by dsimp only; rw [he.2, he.1, Sym2.eq_swap]⟩
      · rcases h with ⟨e, he | he⟩
        · exact ⟨e, by dsimp only; rw [he.1, he.2, Sym2.eq_swap]⟩
        · exact ⟨e, by dsimp only; rw [he.2, he.1]⟩
  have he : Nat.card graph.edgeSet ≤ G.edgeCount := by
    calc
      Nat.card graph.edgeSet ≤ Nat.card (Set.range
          (fun edge : Fin G.edgeCount ↦ s(G.endpoint edge 0, G.endpoint edge 1))) :=
        Nat.card_le_card_of_injective (Set.inclusion hsubset)
          (Set.inclusion_injective hsubset)
      _ ≤ Nat.card (Fin G.edgeCount) :=
        Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
      _ = G.edgeCount := Nat.card_fin _
  have hv : Nat.card (Fin G.vertexCount) = G.vertexCount := Nat.card_fin _
  omega

/-- Summing vertex stability counts each external leg once and each internal
edge twice, including both branches of a loop. -/
theorem stability_sum {S : Type} [Fintype S] (G : StableGraphCode S) :
    3 * G.vertexCount ≤
      2 * (∑ v, G.genus v) + Fintype.card S + 2 * G.edgeCount := by
  classical
  have hlegs : (∑ v, Fintype.card {s : S // G.legVertex s = v}) =
      Fintype.card S := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.legVertex)
  have hhalf : (∑ v, Fintype.card
      {p : Fin G.edgeCount × Fin 2 // G.endpoint p.1 p.2 = v}) =
      2 * G.edgeCount := by
    rw [← Fintype.card_sigma]
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
      Fintype.card_congr (Equiv.sigmaFiberEquiv
        (fun p : Fin G.edgeCount × Fin 2 ↦ G.endpoint p.1 p.2))
  have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) ↦ G.stable v)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm, hlegs, hhalf] using h

/-- Stability bounds the number of vertices by `2g - 2 + n`, written without
truncated subtraction. This is independent of a codimension bound. -/
theorem vertexCount_add_two_le {S : Type} [Fintype S] (G : StableGraphCode S) :
    G.vertexCount + 2 ≤ 2 * G.totalGenus + Fintype.card S := by
  have h := G.stability_sum
  have hv := G.vertexCount_le_edgeCount_add_one
  unfold totalGenus firstBetti
  omega

/-- Every vertex genus is bounded by the arithmetic genus. -/
theorem genus_le_totalGenus {S : Type} [Fintype S] (G : StableGraphCode S)
    (v : Fin G.vertexCount) : G.genus v ≤ G.totalGenus := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset _)) ↦
    Nat.zero_le (G.genus i)) (Finset.mem_univ v)
  unfold totalGenus
  omega

end StableGraphCode

namespace DecoratedStableGraph

variable {S : Type} [Fintype S]

/-- Every edge contributes one to the codimension. -/
theorem edgeCount_le_codimension (G : DecoratedStableGraph S) :
    G.graph.edgeCount ≤ G.codimension := by
  unfold codimension
  omega

/-- The weighted exponent of any individual kappa class is bounded by
stratum codimension. -/
theorem kappa_term_le_codimension (G : DecoratedStableGraph S)
    (v : Fin G.graph.vertexCount) (i : ℕ+) :
    (i : ℕ) * G.kappaPower v i ≤ G.codimension := by
  have hi : (i : ℕ) * G.kappaPower v i ≤
      (G.kappaPower v).sum (fun j p ↦ (j : ℕ) * p) := by
    have h := Finsupp.single_le_sum (G.kappaPower v)
      (g := fun j p ↦ (j : ℕ) * p) (fun _ _ ↦ Nat.zero_le _) i
    simpa only [Finsupp.sum_single_index, mul_zero] using h
  have hv := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset _)) ↦
    Nat.zero_le ((G.kappaPower j).sum (fun k p ↦ (k : ℕ) * p))) (Finset.mem_univ v)
  unfold codimension kappaCodimension
  omega

/-- Kappa exponents are bounded because only positive-index kappa classes
occur in the syntax. -/
theorem kappaPower_le_codimension (G : DecoratedStableGraph S)
    (v : Fin G.graph.vertexCount) (i : ℕ+) : G.kappaPower v i ≤ G.codimension :=
  (Nat.le_mul_of_pos_left _ i.2).trans (G.kappa_term_le_codimension v i)

/-- A kappa index above the codimension has zero exponent. -/
theorem kappaPower_eq_zero_of_codimension_lt (G : DecoratedStableGraph S)
    (v : Fin G.graph.vertexCount) (i : ℕ+) (h : G.codimension < (i : ℕ)) :
    G.kappaPower v i = 0 := by
  by_contra hne
  have hi := (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)).trans
    (G.kappa_term_le_codimension v i)
  omega

/-- External psi exponents are bounded by total codimension. -/
theorem legPsiPower_le_codimension (G : DecoratedStableGraph S) (s : S) :
    G.legPsiPower s ≤ G.codimension := by
  have hs := Finset.single_le_sum (fun t (_ : t ∈ (Finset.univ : Finset S)) ↦
    Nat.zero_le (G.legPsiPower t)) (Finset.mem_univ s)
  unfold codimension legPsiCodimension
  omega

/-- Internal psi exponents are bounded by total codimension. -/
theorem halfEdgePsiPower_le_codimension (G : DecoratedStableGraph S)
    (e : Fin G.graph.edgeCount) (i : Fin 2) : G.halfEdgePsiPower e i ≤ G.codimension := by
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) ↦
    Nat.zero_le (G.halfEdgePsiPower e j)) (Finset.mem_univ i)
  have he := Finset.single_le_sum (fun edge (_ : edge ∈ (Finset.univ : Finset _)) ↦
    Nat.zero_le (∑ j, G.halfEdgePsiPower edge j)) (Finset.mem_univ e)
  unfold codimension halfEdgePsiCodimension
  omega

end DecoratedStableGraph
end AxiomaticGW
