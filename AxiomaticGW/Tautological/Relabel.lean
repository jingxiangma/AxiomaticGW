/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphIsomorphisms
public import AxiomaticGW.Tautological.StrataModule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# External label transport on decorated strata

This is the finite-presentation version of the existing stable-graph
relabelling. Incidence and external powers are transported together;
internal graph data and raw coefficients are unchanged. The explicit
labelled boundary relations use this operation before certificate replay.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace StableGraphCode

variable {S T U : Type} [Fintype S] [Fintype T] [Fintype U]

/-- Reuse the existing stable-graph transport without changing finite blocks. -/
def relabel (G : StableGraphCode S) (e : S ≃ T) : StableGraphCode T where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount
  vertexCount_pos := G.vertexCount_pos
  legVertex := G.legVertex ∘ e.symm
  endpoint := G.endpoint
  genus := G.genus
  connected := G.connected
  stable := (G.toStableGraph.relabel e).stable

/-- Relabelling leaves the arithmetic genus unchanged. -/
theorem relabel_totalGenus (G : StableGraphCode S) (e : S ≃ T) :
    (G.relabel e).totalGenus = G.totalGenus := rfl

/-- Identity transport leaves the graph presentation unchanged. -/
theorem relabel_refl (G : StableGraphCode S) : G.relabel (Equiv.refl S) = G := rfl

/-- Label transport composes in the covariant direction. -/
theorem relabel_trans (G : StableGraphCode S) (e : S ≃ T) (f : T ≃ U) :
    (G.relabel e).relabel f = G.relabel (e.trans f) := rfl

/-- Label-fixing graph isomorphisms transport with the same finite bijections. -/
def Iso.relabel {G H : StableGraphCode S} (h : Iso G H) (e : S ≃ T) :
    Iso (G.relabel e) (H.relabel e) where
  vertexEquiv := h.vertexEquiv
  edgeEquiv := h.edgeEquiv
  branchEquiv := h.branchEquiv
  legVertex_comm := fun t ↦ h.legVertex_comm (e.symm t)
  endpoint_comm := h.endpoint_comm
  genus_comm := h.genus_comm

end StableGraphCode

namespace DecoratedStableGraph

variable {S T U : Type} [Fintype S] [Fintype T] [Fintype U]

/-- Transport external incidence and psi powers with the same label inverse. -/
def relabel (G : DecoratedStableGraph S) (e : S ≃ T) : DecoratedStableGraph T where
  graph := G.graph.relabel e
  kappaPower := G.kappaPower
  legPsiPower := G.legPsiPower ∘ e.symm
  halfEdgePsiPower := G.halfEdgePsiPower

/-- Identity transport fixes the decorated presentation. -/
theorem relabel_refl (G : DecoratedStableGraph S) : G.relabel (Equiv.refl S) = G := rfl

/-- Powers and incidence compose with the same covariant label transport. -/
theorem relabel_trans (G : DecoratedStableGraph S) (e : S ≃ T) (f : T ≃ U) :
    (G.relabel e).relabel f = G.relabel (e.trans f) := rfl

/-- Reindexing external labels does not change the sum of decoration degrees. -/
theorem relabel_codimension (G : DecoratedStableGraph S) (e : S ≃ T) :
    (G.relabel e).codimension = G.codimension := by
  have hs : (∑ t, G.legPsiPower (e.symm t)) = ∑ s, G.legPsiPower s :=
    e.symm.sum_comp G.legPsiPower
  change G.graph.edgeCount + G.kappaCodimension +
    (∑ t, G.legPsiPower (e.symm t)) + G.halfEdgePsiCodimension = _
  rw [hs]
  rfl

/-- Every decorated isomorphism transports along a label equivalence. -/
def Iso.relabel {G H : DecoratedStableGraph S} (h : Iso G H) (e : S ≃ T) :
    Iso (G.relabel e) (H.relabel e) where
  graphIso := h.graphIso.relabel e
  kappaPower_comm := h.kappaPower_comm
  legPsiPower_comm := fun t ↦ h.legPsiPower_comm (e.symm t)
  halfEdgePsiPower_comm := h.halfEdgePsiPower_comm

/-- An isomorphism after a bijective label change fixes the original labels. -/
def Iso.unrelabel {G H : DecoratedStableGraph S} {e : S ≃ T}
    (h : Iso (G.relabel e) (H.relabel e)) : Iso G H where
  graphIso := show StableGraphCode.Iso G.graph H.graph from
    { vertexEquiv := h.graphIso.vertexEquiv
      edgeEquiv := h.graphIso.edgeEquiv
      branchEquiv := h.graphIso.branchEquiv
      legVertex_comm := fun s ↦ by
        have ht := h.graphIso.legVertex_comm (e s)
        change h.graphIso.vertexEquiv (G.graph.legVertex (e.symm (e s))) =
          H.graph.legVertex (e.symm (e s)) at ht
        rw [Equiv.symm_apply_apply] at ht
        exact ht
      endpoint_comm := h.graphIso.endpoint_comm
      genus_comm := h.graphIso.genus_comm }
  kappaPower_comm := h.kappaPower_comm
  legPsiPower_comm := fun s ↦ by
    simpa only [DecoratedStableGraph.relabel, Function.comp_apply, Equiv.symm_apply_apply]
      using h.legPsiPower_comm (e s)
  halfEdgePsiPower_comm := h.halfEdgePsiPower_comm

/-- Relabelling gives a bijection of all decorated isomorphism witnesses. -/
def relabelIsoEquiv (G H : DecoratedStableGraph S) (e : S ≃ T) :
    Iso G H ≃ Iso (G.relabel e) (H.relabel e) where
  toFun h := h.relabel e
  invFun := Iso.unrelabel
  left_inv _ := Iso.ext rfl
  right_inv _ := Iso.ext rfl

/-- Label transport preserves the full automorphism order, including loops. -/
theorem relabel_automorphismCount (G : DecoratedStableGraph S) (e : S ≃ T) :
    (G.relabel e).automorphismCount = G.automorphismCount := by
  letI := isoFintype G G
  letI := isoFintype (G.relabel e) (G.relabel e)
  rw [automorphismCount_eq_card, automorphismCount_eq_card]
  exact (Fintype.card_congr (relabelIsoEquiv G G e)).symm

end DecoratedStableGraph

namespace TautologicalStratum

variable {g : ℕ} {S T U : Type} [Fintype S] [Fintype T] [Fintype U]

/-- Bijective external label transport on graph isomorphism classes. -/
def relabel (x : TautologicalStratum g S) (e : S ≃ T) : TautologicalStratum g T :=
  Quotient.map (fun G ↦ ⟨G.1.relabel e, G.2⟩) (fun _ _ h ↦ by
    obtain ⟨h⟩ := h
    exact ⟨h.relabel e⟩) x

/-- The quotient transport computes on a chosen finite presentation. -/
theorem relabel_mk (G : DecoratedStableGraph S) (h : G.graph.totalGenus = g) (e : S ≃ T) :
    (mk G h).relabel e = mk (G.relabel e) h := rfl

/-- Identity label transport fixes each graph class. -/
theorem relabel_refl (x : TautologicalStratum g S) : x.relabel (Equiv.refl S) = x := by
  refine Quotient.inductionOn x ?_
  intro G
  rfl

/-- Successive quotient transports compose in the same direction as the labels. -/
theorem relabel_trans (x : TautologicalStratum g S) (e : S ≃ T) (f : T ≃ U) :
    (x.relabel e).relabel f = x.relabel (e.trans f) := by
  refine Quotient.inductionOn x ?_
  intro G
  rfl

/-- Isomorphism classes preserve codimension under a label bijection. -/
theorem relabel_codimension (x : TautologicalStratum g S) (e : S ≃ T) :
    (x.relabel e).codimension = x.codimension := by
  refine Quotient.inductionOn x ?_
  intro G
  exact G.1.relabel_codimension e

/-- Relabelling cannot identify different labelled graph classes. -/
theorem relabel_injective (e : S ≃ T) :
    Function.Injective (fun x : TautologicalStratum g S ↦ x.relabel e) := by
  intro x y h
  have hi := congrArg (fun z ↦ z.relabel e.symm) h
  simpa only [relabel_trans, Equiv.self_trans_symm, relabel_refl] using hi

end TautologicalStratum

namespace StrataModule

variable {g : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-- Relabel rational combinations without changing their raw coefficients. -/
noncomputable def relabel (e : S ≃ T) : StrataModule g S →ₗ[ℚ] StrataModule g T :=
  Finsupp.linearCombination ℚ (fun x ↦ basis (x.relabel e))

/-- A single coefficient keeps its value in the relabelled graph class. -/
theorem relabel_single (e : S ≃ T) (x : TautologicalStratum g S) (q : ℚ) :
    relabel e (Finsupp.single x q) = q • basis (x.relabel e) :=
  Finsupp.linearCombination_single _ _ _

/-- Basis transport agrees with the graph quotient transport. -/
theorem relabel_basis (e : S ≃ T) (x : TautologicalStratum g S) :
    relabel e (basis x) = basis (x.relabel e) := by
  rw [basis, relabel_single, one_smul]

/-- Labelled transport preserves homogeneous degree subspaces. -/
theorem relabel_mem_degree (e : S ≃ T) {d : ℕ} {r : StrataModule g S}
    (hr : r ∈ degree d) : relabel e r ∈ degree d := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    rw [relabel_basis, ← hx, ← TautologicalStratum.relabel_codimension x e]
    exact basis_mem_degree _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul q a _ ha => rw [map_smul]; exact Submodule.smul_mem _ q ha

end StrataModule

end AxiomaticGW
