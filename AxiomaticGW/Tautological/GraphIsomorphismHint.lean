/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphIsomorphisms

/-!
# Checking proposed decorated graph isomorphisms

Large replay frames should check supplied finite bijections rather than
repeat permutation searches in the kernel. A hint supplies images of vertices
and edges and a branch swap at each source edge. The checker verifies lengths,
bounds, bijectivity, incidence, genera and every decoration. Its soundness
theorem returns the existing decorated-isomorphism proposition.
-/

@[expose] public section

namespace AxiomaticGW

/-- Untrusted images of vertices, edges and ordered edge branches. -/
structure GraphIsomorphismHint where
  /-- Target vertex indices, in source vertex order. -/
  vertices : List ℕ
  /-- Target edge indices, in source edge order. -/
  edges : List ℕ
  /-- At each source edge, `true` exchanges branches zero and one. -/
  swaps : List Bool

namespace GraphIsomorphismHint

/-- Total finite lookup. The checker separately requires every entry to be in bounds. -/
def finiteMap (a : List ℕ) {m n : ℕ} (h : m = n) (i : Fin m) : Fin n :=
  Fin.cast h ⟨a.getD i.val 0 % m,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- An edge may retain or exchange its two ordered branches. -/
def branch (h : GraphIsomorphismHint) (e : ℕ) : Equiv.Perm (Fin 2) :=
  if h.swaps.getD e false then Equiv.swap 0 1 else Equiv.refl _

variable {S : Type} [Fintype S]

/-- The complete finite checks, with no search for a different proposed bijection. -/
def Valid (h : GraphIsomorphismHint) (G H : DecoratedStableGraph S)
    (hc : G.graph.vertexCount = H.graph.vertexCount ∧ G.graph.edgeCount = H.graph.edgeCount) :
    Prop :=
  h.vertices.length = G.graph.vertexCount ∧ h.edges.length = G.graph.edgeCount ∧
  h.swaps.length = G.graph.edgeCount ∧
  (∀ v : Fin G.graph.vertexCount, h.vertices.getD v.val 0 < H.graph.vertexCount) ∧
  (∀ e : Fin G.graph.edgeCount, h.edges.getD e.val 0 < H.graph.edgeCount) ∧
  Function.Bijective (finiteMap h.vertices hc.1) ∧
  Function.Bijective (finiteMap h.edges hc.2) ∧
  (∀ s, finiteMap h.vertices hc.1 (G.graph.legVertex s) = H.graph.legVertex s) ∧
  (∀ e b, finiteMap h.vertices hc.1 (G.graph.endpoint e b) =
    H.graph.endpoint (finiteMap h.edges hc.2 e) (h.branch e.val b)) ∧
  (∀ v, H.graph.genus (finiteMap h.vertices hc.1 v) = G.graph.genus v) ∧
  (∀ v, H.kappaPower (finiteMap h.vertices hc.1 v) = G.kappaPower v) ∧
  (∀ s, H.legPsiPower s = G.legPsiPower s) ∧
  (∀ e b, H.halfEdgePsiPower (finiteMap h.edges hc.2 e) (h.branch e.val b) =
    G.halfEdgePsiPower e b)

instance (h : GraphIsomorphismHint) (G H : DecoratedStableGraph S) (hc) :
    Decidable (h.Valid G H hc) := by
  unfold Valid
  infer_instance

/-- Reject shape mismatches before checking the proposed maps and decorations. -/
def check (h : GraphIsomorphismHint) (G H : DecoratedStableGraph S) : Bool :=
  if hc : G.graph.vertexCount = H.graph.vertexCount ∧ G.graph.edgeCount = H.graph.edgeCount then
    decide (h.Valid G H hc)
  else false

/-- An accepted hint gives an actual decorated graph isomorphism. -/
theorem check_sound (h : GraphIsomorphismHint) (G H : DecoratedStableGraph S)
    (hh : h.check G H = true) : G.isomorphic? H = true := by
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff G H).mpr
  unfold check at hh
  split at hh
  · rename_i hc
    rcases of_decide_eq_true hh with
      ⟨_, _, _, _, _, hv, he, hl, hn, hg, hk, hp, hq⟩
    exact ⟨{
      graphIso := {
        vertexEquiv := Equiv.ofBijective (finiteMap h.vertices hc.1) hv
        edgeEquiv := Equiv.ofBijective (finiteMap h.edges hc.2) he
        branchEquiv := fun e ↦ h.branch e.val
        legVertex_comm := hl
        endpoint_comm := hn
        genus_comm := hg }
      kappaPower_comm := fun v i ↦ DFunLike.congr_fun (hk v) i
      legPsiPower_comm := hp
      halfEdgePsiPower_comm := hq }⟩
  · exact Bool.noConfusion hh

end GraphIsomorphismHint
end AxiomaticGW
