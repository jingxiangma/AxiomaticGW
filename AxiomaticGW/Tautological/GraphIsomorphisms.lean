/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedStableGraph
public import Mathlib.Data.Fintype.Perm

/-!
# Finite enumeration of graph isomorphisms

The finite vertex and edge presentations allow exhaustive enumeration of
isomorphisms. Each candidate consists of a vertex equivalence, an edge
equivalence, and an independent permutation of the two branches of every
edge. Filtering these candidates gives a computable isomorphism test and
automorphism count. The equivalences with the existing `Iso` structures
prove completeness, including branch exchanges on loops.

This file counts automorphisms of a given presentation. It does not enumerate
all stable graphs of prescribed genus, markings, and codimension.
-/

@[expose] public section

namespace AxiomaticGW

namespace StableGraphCode

variable {S : Type} [Fintype S]

/-- Finite bijective data to be checked for preservation of graph structure. -/
abbrev IsoCandidate (G H : StableGraphCode S) :=
  (Fin G.vertexCount ≃ Fin H.vertexCount) ×
    (Fin G.edgeCount ≃ Fin H.edgeCount) ×
      (Fin G.edgeCount → Equiv.Perm (Fin 2))

/-- The incidence and genus tests for a candidate graph isomorphism. -/
def IsoCandidate.Preserves {G H : StableGraphCode S} (c : IsoCandidate G H) : Prop :=
  (∀ s, c.1 (G.legVertex s) = H.legVertex s) ∧
    (∀ e i, c.1 (G.endpoint e i) = H.endpoint (c.2.1 e) (c.2.2 e i)) ∧
      (∀ v, H.genus (c.1 v) = G.genus v)

instance {G H : StableGraphCode S} (c : IsoCandidate G H) :
    Decidable c.Preserves :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- Forget the preservation proofs in an isomorphism. -/
def Iso.toCandidate {G H : StableGraphCode S} (e : Iso G H) : IsoCandidate G H :=
  (e.vertexEquiv, e.edgeEquiv, e.branchEquiv)

/-- A candidate passing the finite tests gives an actual graph isomorphism. -/
def IsoCandidate.toIso {G H : StableGraphCode S} (c : IsoCandidate G H)
    (h : c.Preserves) : Iso G H where
  vertexEquiv := c.1
  edgeEquiv := c.2.1
  branchEquiv := c.2.2
  legVertex_comm := h.1
  endpoint_comm := h.2.1
  genus_comm := h.2.2

/-- Enumerate all candidates that preserve the graph structure. -/
def isoCandidates (G H : StableGraphCode S) : Finset (IsoCandidate G H) :=
  Finset.univ.filter IsoCandidate.Preserves

theorem mem_isoCandidates_iff {G H : StableGraphCode S} (c : IsoCandidate G H) :
    c ∈ isoCandidates G H ↔ c.Preserves := by
  simp only [isoCandidates, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Enumeration is equivalent to the existing isomorphism type, with no
identification of distinct branch permutations. -/
def isoEquivCandidates (G H : StableGraphCode S) :
    Iso G H ≃ {c // c ∈ isoCandidates G H} where
  toFun e := ⟨e.toCandidate, (mem_isoCandidates_iff _).2
    ⟨e.legVertex_comm, e.endpoint_comm, e.genus_comm⟩⟩
  invFun c := c.1.toIso ((mem_isoCandidates_iff _).1 c.2)
  left_inv e := by cases e; rfl
  right_inv c := by apply Subtype.ext; rfl

/-- Explicit finite enumeration of the isomorphism type. This is data rather
than an additional global typeclass instance. -/
@[implicit_reducible]
def isoFintype (G H : StableGraphCode S) : Fintype (Iso G H) :=
  Fintype.ofEquiv {c // c ∈ isoCandidates G H} (isoEquivCandidates G H).symm

theorem isomorphic_iff_candidates_nonempty (G H : StableGraphCode S) :
    Isomorphic G H ↔ (isoCandidates G H).Nonempty := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(isoEquivCandidates G H e).1, (isoEquivCandidates G H e).2⟩
  · rintro ⟨c, hc⟩
    exact ⟨(isoEquivCandidates G H).symm ⟨c, hc⟩⟩

/-- Isomorphisms preserve the partition of external legs among vertices. -/
theorem Iso.legVertex_eq_iff {G H : StableGraphCode S} (e : Iso G H) (s t : S) :
    G.legVertex s = G.legVertex t ↔ H.legVertex s = H.legVertex t := by
  rw [← e.legVertex_comm s, ← e.legVertex_comm t]
  exact e.vertexEquiv.injective.eq_iff.symm

/-- Executable test for label-preserving graph isomorphism. Size and external
leg-partition tests reject incompatible data before permutation search.
Automorphism counting still enumerates all witnesses. -/
def isomorphic? (G H : StableGraphCode S) : Bool :=
  decide (G.vertexCount = H.vertexCount ∧ G.edgeCount = H.edgeCount ∧
    (∀ s t, G.legVertex s = G.legVertex t ↔ H.legVertex s = H.legVertex t) ∧
    ∃ vertex : Fin G.vertexCount ≃ Fin H.vertexCount,
    (∀ s, vertex (G.legVertex s) = H.legVertex s) ∧
    (∀ v, H.genus (vertex v) = G.genus v) ∧
    ∃ edge : Fin G.edgeCount ≃ Fin H.edgeCount,
    ∃ branch : Fin G.edgeCount → Equiv.Perm (Fin 2),
      ∀ e i, vertex (G.endpoint e i) = H.endpoint (edge e) (branch e i))

theorem isomorphic?_eq_true_iff (G H : StableGraphCode S) :
    isomorphic? G H = true ↔ Isomorphic G H := by
  rw [isomorphic?, decide_eq_true_eq]
  constructor
  · rintro ⟨_, _, _, vertex, hleg, hgenus, edge, branch, hendpoint⟩
    exact ⟨⟨vertex, edge, branch, hleg, hendpoint, hgenus⟩⟩
  · rintro ⟨iso⟩
    exact ⟨iso.vertexCount_eq, iso.edgeCount_eq, iso.legVertex_eq_iff,
      iso.vertexEquiv, iso.legVertex_comm, iso.genus_comm,
      iso.edgeEquiv, iso.branchEquiv, iso.endpoint_comm⟩

/-- Number of graph automorphisms, including independent loop branch swaps. -/
def automorphismCount (G : StableGraphCode S) : ℕ :=
  (isoCandidates G G).card

theorem automorphismCount_eq_card (G : StableGraphCode S) :
    G.automorphismCount = @Fintype.card (Iso G G) (isoFintype G G) := by
  letI := isoFintype G G
  simpa only [Fintype.card_coe, automorphismCount] using
    (Fintype.card_congr (isoEquivCandidates G G)).symm

theorem automorphismCount_pos (G : StableGraphCode S) :
    0 < G.automorphismCount := by
  apply Finset.card_pos.mpr
  exact (isomorphic_iff_candidates_nonempty G G).1 (isomorphic_refl G)

/-- Graph isomorphisms are determined by their three finite equivalences. -/
theorem Iso.ext {G H : StableGraphCode S} {e f : Iso G H}
    (hv : e.vertexEquiv = f.vertexEquiv) (he : e.edgeEquiv = f.edgeEquiv)
    (hb : e.branchEquiv = f.branchEquiv) : e = f := by
  cases e
  cases f
  cases hv
  cases he
  cases hb
  rfl

/-- Changing presentation conjugates the automorphisms bijectively. -/
def Iso.automorphismEquiv {G H : StableGraphCode S} (e : Iso G H) :
    Iso G G ≃ Iso H H where
  toFun a := (e.symm.trans a).trans e
  invFun a := (e.trans a).trans e.symm
  left_inv a := by
    apply Iso.ext
    · apply Equiv.ext
      intro v
      simp only [Iso.trans, Iso.symm, Equiv.trans_apply,
        Equiv.symm_apply_apply]
    · apply Equiv.ext
      intro edge
      simp only [Iso.trans, Iso.symm, Equiv.trans_apply,
        Equiv.symm_apply_apply]
    · funext edge
      apply Equiv.ext
      intro i
      simp only [Iso.trans, Iso.symm, Equiv.trans_apply,
        Equiv.symm_apply_apply]
  right_inv a := by
    apply Iso.ext
    · apply Equiv.ext
      intro v
      simp only [Iso.trans, Iso.symm, Equiv.trans_apply,
        Equiv.apply_symm_apply]
    · apply Equiv.ext
      intro edge
      simp only [Iso.trans, Iso.symm, Equiv.trans_apply,
        Equiv.apply_symm_apply]
    · funext edge
      apply Equiv.ext
      intro i
      simp only [Iso.trans, Iso.symm, Equiv.trans_apply,
        Equiv.apply_symm_apply]

theorem Iso.automorphismCount_eq {G H : StableGraphCode S} (e : Iso G H) :
    G.automorphismCount = H.automorphismCount := by
  letI := isoFintype G G
  letI := isoFintype H H
  rw [automorphismCount_eq_card, automorphismCount_eq_card]
  exact Fintype.card_congr e.automorphismEquiv

end StableGraphCode

namespace DecoratedStableGraph

variable {S : Type} [Fintype S]

/-- A candidate preserves a decorated graph when it preserves the graph and
all decorations. Equality of the finitely supported kappa exponents makes
this test executable without quantifying over every positive integer. -/
def Preserves (G H : DecoratedStableGraph S)
    (c : StableGraphCode.IsoCandidate G.graph H.graph) : Prop :=
  c.Preserves ∧
    (∀ v, H.kappaPower (c.1 v) = G.kappaPower v) ∧
      (∀ s, H.legPsiPower s = G.legPsiPower s) ∧
        (∀ e i, H.halfEdgePsiPower (c.2.1 e) (c.2.2 e i) = G.halfEdgePsiPower e i)

instance (G H : DecoratedStableGraph S)
    (c : StableGraphCode.IsoCandidate G.graph H.graph) : Decidable (Preserves G H c) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- Enumerate candidates preserving incidence, genus, and decorations. -/
def isoCandidates (G H : DecoratedStableGraph S) :
    Finset (StableGraphCode.IsoCandidate G.graph H.graph) :=
  Finset.univ.filter (Preserves G H)

theorem mem_isoCandidates_iff (G H : DecoratedStableGraph S)
    (c : StableGraphCode.IsoCandidate G.graph H.graph) :
    c ∈ isoCandidates G H ↔ Preserves G H c := by
  simp only [isoCandidates, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The finite enumeration has exactly the existing decorated isomorphisms. -/
def isoEquivCandidates (G H : DecoratedStableGraph S) :
    Iso G H ≃ {c // c ∈ isoCandidates G H} where
  toFun e := ⟨e.graphIso.toCandidate, (mem_isoCandidates_iff G H _).2
    ⟨⟨e.graphIso.legVertex_comm, e.graphIso.endpoint_comm, e.graphIso.genus_comm⟩,
      fun v ↦ Finsupp.ext (e.kappaPower_comm v),
      e.legPsiPower_comm, e.halfEdgePsiPower_comm⟩⟩
  invFun c :=
    let h := (mem_isoCandidates_iff G H c.1).1 c.2
    { graphIso := c.1.toIso h.1
      kappaPower_comm := fun v i ↦ DFunLike.congr_fun (h.2.1 v) i
      legPsiPower_comm := h.2.2.1
      halfEdgePsiPower_comm := h.2.2.2 }
  left_inv e := by cases e; rfl
  right_inv c := by apply Subtype.ext; rfl

/-- Explicit finite enumeration of decorated isomorphisms. -/
@[implicit_reducible]
def isoFintype (G H : DecoratedStableGraph S) : Fintype (Iso G H) :=
  Fintype.ofEquiv {c // c ∈ isoCandidates G H} (isoEquivCandidates G H).symm

theorem isomorphic_iff_candidates_nonempty (G H : DecoratedStableGraph S) :
    Isomorphic G H ↔ (isoCandidates G H).Nonempty := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(isoEquivCandidates G H e).1, (isoEquivCandidates G H e).2⟩
  · rintro ⟨c, hc⟩
    exact ⟨(isoEquivCandidates G H).symm ⟨c, hc⟩⟩

/-- Executable decorated-isomorphism search. Size and external leg tests
precede the degree computation and vertex, edge, and branch bijections.
The search stops at its first witness; automorphism counting retains all
witnesses. -/
def isomorphic? (G H : DecoratedStableGraph S) : Bool :=
  decide (G.graph.vertexCount = H.graph.vertexCount ∧
    G.graph.edgeCount = H.graph.edgeCount ∧
    (∀ s, H.legPsiPower s = G.legPsiPower s) ∧
    (∀ s t, G.graph.legVertex s = G.graph.legVertex t ↔
      H.graph.legVertex s = H.graph.legVertex t) ∧
    G.codimension = H.codimension ∧
    ∃ vertex : Fin G.graph.vertexCount ≃ Fin H.graph.vertexCount,
      (∀ s, vertex (G.graph.legVertex s) = H.graph.legVertex s) ∧
      (∀ v, H.graph.genus (vertex v) = G.graph.genus v) ∧
      (∀ v, H.kappaPower (vertex v) = G.kappaPower v) ∧
      ∃ edge : Fin G.graph.edgeCount ≃ Fin H.graph.edgeCount,
      ∃ branch : Fin G.graph.edgeCount → Equiv.Perm (Fin 2),
        (∀ e i, vertex (G.graph.endpoint e i) =
          H.graph.endpoint (edge e) (branch e i)) ∧
        (∀ e i, H.halfEdgePsiPower (edge e) (branch e i) = G.halfEdgePsiPower e i))

theorem isomorphic?_eq_true_iff (G H : DecoratedStableGraph S) :
    isomorphic? G H = true ↔ Isomorphic G H := by
  rw [isomorphic?, decide_eq_true_eq]
  constructor
  · rintro ⟨_, _, hpsi, _, _, vertex, hleg, hgenus, hkappa,
      edge, branch, hendpoint, hhalf⟩
    exact ⟨{ graphIso := ⟨vertex, edge, branch, hleg, hendpoint, hgenus⟩
             kappaPower_comm := fun v i ↦ DFunLike.congr_fun (hkappa v) i
             legPsiPower_comm := hpsi
             halfEdgePsiPower_comm := hhalf }⟩
  · rintro ⟨iso⟩
    exact ⟨iso.graphIso.vertexCount_eq, iso.graphIso.edgeCount_eq,
      iso.legPsiPower_comm, iso.graphIso.legVertex_eq_iff, iso.codimension_eq,
      iso.graphIso.vertexEquiv,
      iso.graphIso.legVertex_comm, iso.graphIso.genus_comm,
      fun v ↦ Finsupp.ext (iso.kappaPower_comm v),
      iso.graphIso.edgeEquiv, iso.graphIso.branchEquiv,
      iso.graphIso.endpoint_comm, iso.halfEdgePsiPower_comm⟩

/-- Number of automorphisms preserving all decorations. -/
def automorphismCount (G : DecoratedStableGraph S) : ℕ :=
  (isoCandidates G G).card

theorem automorphismCount_eq_card (G : DecoratedStableGraph S) :
    G.automorphismCount = @Fintype.card (Iso G G) (isoFintype G G) := by
  letI := isoFintype G G
  simpa only [Fintype.card_coe, automorphismCount] using
    (Fintype.card_congr (isoEquivCandidates G G)).symm

theorem automorphismCount_pos (G : DecoratedStableGraph S) :
    0 < G.automorphismCount := by
  apply Finset.card_pos.mpr
  exact (isomorphic_iff_candidates_nonempty G G).1 (isomorphic_refl G)

/-- All decoration preservation fields are propositions, so the underlying
graph isomorphism determines the decorated isomorphism. -/
theorem Iso.ext {G H : DecoratedStableGraph S} {e f : Iso G H}
    (h : e.graphIso = f.graphIso) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- Conjugation gives a bijection of decoration-preserving automorphisms. -/
def Iso.automorphismEquiv {G H : DecoratedStableGraph S} (e : Iso G H) :
    Iso G G ≃ Iso H H where
  toFun a := (e.symm.trans a).trans e
  invFun a := (e.trans a).trans e.symm
  left_inv a := by
    apply Iso.ext
    exact e.graphIso.automorphismEquiv.left_inv a.graphIso
  right_inv a := by
    apply Iso.ext
    exact e.graphIso.automorphismEquiv.right_inv a.graphIso

/-- The automorphism count is independent of the finite presentation. -/
theorem Iso.automorphismCount_eq {G H : DecoratedStableGraph S} (e : Iso G H) :
    G.automorphismCount = H.automorphismCount := by
  letI := isoFintype G G
  letI := isoFintype H H
  rw [automorphismCount_eq_card, automorphismCount_eq_card]
  exact Fintype.card_congr e.automorphismEquiv

end DecoratedStableGraph

namespace TautologicalStratum

/-- A successful finite isomorphism check certifies equality of the
associated formal stratum classes. -/
theorem mk_eq_mk_of_isomorphic? {g : ℕ} {S : Type} [Fintype S]
    {G H : DecoratedStableGraph S} (hG : G.graph.totalGenus = g)
    (hH : H.graph.totalGenus = g) (h : DecoratedStableGraph.isomorphic? G H = true) :
    mk G hG = mk H hH :=
  mk_eq_mk hG hH ((DecoratedStableGraph.isomorphic?_eq_true_iff G H).1 h)

end TautologicalStratum

end AxiomaticGW
