/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphBounds
public import AxiomaticGW.Tautological.StrataModule
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Separating gluing of decorated stable graphs

Two connected components, each with one distinguished `none` marking, are
joined by a new last edge. The first component occupies the initial vertex
and edge blocks; the second occupies the following blocks. Node powers move
to branches zero and one. Every old decoration and retained label survives.
The convention is raw graph pushforward, without automorphism division.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace StableGraphCode

variable {S T : Type} [Fintype S] [Fintype T]

/-- The flags of two components become retained labels and the flags of
the old edges plus the new last edge. -/
def separatingFlagsEquiv (S T : Type) (m n : ℕ) :
    (Option S ⊕ (Fin m × Fin 2)) ⊕ (Option T ⊕ (Fin n × Fin 2)) ≃
      (S ⊕ T) ⊕ (Fin (m + n + 1) × Fin 2) where
  toFun
    | .inl (.inl none) => .inr (Fin.last (m + n), 0)
    | .inl (.inl (some s)) => .inl (.inl s)
    | .inl (.inr (e, i)) => .inr ((finSumFinEquiv (.inl e)).castSucc, i)
    | .inr (.inl none) => .inr (Fin.last (m + n), 1)
    | .inr (.inl (some t)) => .inl (.inr t)
    | .inr (.inr (e, i)) => .inr ((finSumFinEquiv (.inr e)).castSucc, i)
  invFun
    | .inl (.inl s) => .inl (.inl (some s))
    | .inl (.inr t) => .inr (.inl (some t))
    | .inr (e, i) => Fin.lastCases
        (Fin.cases (.inl (.inl none)) (fun _ ↦ .inr (.inl none)) i)
        (fun e ↦ Sum.elim (fun e ↦ .inl (.inr (e, i)))
          (fun e ↦ .inr (.inr (e, i))) (finSumFinEquiv.symm e)) e
  left_inv x := by
    rcases x with ((_ | s) | ⟨e, i⟩) | ((_ | t) | ⟨e, i⟩)
    all_goals simp only [Fin.lastCases_last, Fin.lastCases_castSucc,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] <;> rfl
  right_inv x := by
    rcases x with (s | t) | ⟨e, i⟩
    · rfl
    · rfl
    · cases e using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; fin_cases i <;> rfl
      | cast e =>
        simp only [Fin.lastCases_castSucc]
        obtain ⟨e, rfl⟩ := finSumFinEquiv.surjective e
        rcases e with e | e <;> simp only [Equiv.symm_apply_apply] <;> rfl

/-- The new edge joins the two `none` legs; old edges keep their ordered
endpoints in the corresponding vertex block. -/
def separatingEndpoint (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) :
    Fin (G.edgeCount + H.edgeCount + 1) → Fin 2 → Fin (G.vertexCount + H.vertexCount) :=
  Fin.lastCases
    (Fin.cases (finSumFinEquiv (.inl (G.legVertex none)))
      (fun _ ↦ finSumFinEquiv (.inr (H.legVertex none))))
    (fun e i ↦ finSumFinEquiv (Sum.elim
      (fun e ↦ .inl (G.endpoint e i)) (fun e ↦ .inr (H.endpoint e i))
        (finSumFinEquiv.symm e)))

/-- Vertex of each source flag, in the combined vertex presentation. -/
def separatingSourceVertex (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) :
    (Option S ⊕ (Fin G.edgeCount × Fin 2)) ⊕
      (Option T ⊕ (Fin H.edgeCount × Fin 2)) → Fin (G.vertexCount + H.vertexCount) :=
  Sum.elim
    (fun f ↦ finSumFinEquiv (.inl (Sum.elim G.legVertex (fun p ↦ G.endpoint p.1 p.2) f)))
    (fun f ↦ finSumFinEquiv (.inr (Sum.elim H.legVertex (fun p ↦ H.endpoint p.1 p.2) f)))

/-- Vertex of each target flag, before constructing the glued graph. -/
def separatingTargetVertex (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) :
    (S ⊕ T) ⊕ (Fin (G.edgeCount + H.edgeCount + 1) × Fin 2) →
      Fin (G.vertexCount + H.vertexCount) :=
  Sum.elim
    (Sum.elim (fun s ↦ finSumFinEquiv (.inl (G.legVertex (some s))))
      (fun t ↦ finSumFinEquiv (.inr (H.legVertex (some t)))))
    (fun p ↦ separatingEndpoint G H p.1 p.2)

/-- The flag bijection preserves incidence, including both new node flags. -/
theorem separating_flags_vertex (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) (f) :
    separatingTargetVertex G H (separatingFlagsEquiv S T G.edgeCount H.edgeCount f) =
      separatingSourceVertex G H f := by
  rcases f with ((_ | s) | ⟨e, i⟩) | ((_ | t) | ⟨e, i⟩)
  all_goals simp only [separatingTargetVertex, separatingSourceVertex,
    separatingFlagsEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
    separatingEndpoint, Fin.lastCases_last, Fin.lastCases_castSucc,
    Equiv.symm_apply_apply] <;> rfl

/-- Gluing preserves exactly the flags at each vertex of either component.
The other component contributes an empty fibre. -/
def separatingFlagFiberEquiv (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) (v : Fin G.vertexCount ⊕ Fin H.vertexCount) :
    Sum.elim G.toStableGraph.VertexLabel H.toStableGraph.VertexLabel v ≃
      {f // separatingTargetVertex G H f = finSumFinEquiv v} := by
  let e := (separatingFlagsEquiv S T G.edgeCount H.edgeCount).subtypeEquiv
    (p := fun f ↦ separatingSourceVertex G H f = finSumFinEquiv v)
    (q := fun f ↦ separatingTargetVertex G H f = finSumFinEquiv v)
    (fun f ↦ by rw [separating_flags_vertex])
  rcases v with v | v
  · letI : IsEmpty {f : Option T ⊕ (Fin H.edgeCount × Fin 2) //
        separatingSourceVertex G H (.inr f) = finSumFinEquiv (.inl v)} :=
      ⟨fun x ↦ by
        have h := finSumFinEquiv.injective x.2
        exact Sum.inr_ne_inl h⟩
    let ev := (Equiv.subtypeEquivRight
      (p := fun f : Option S ⊕ (Fin G.edgeCount × Fin 2) ↦
        separatingSourceVertex G H (.inl f) = finSumFinEquiv (.inl v))
      (q := fun f ↦ Sum.elim G.legVertex (fun p ↦ G.endpoint p.1 p.2) f = v)
      (fun f ↦ by
      simp only [separatingSourceVertex, Sum.elim_inl, Equiv.apply_eq_iff_eq,
        Sum.inl.injEq])).trans Equiv.subtypeSum
    exact ((Equiv.subtypeSum.trans (ev.sumCongr (Equiv.refl _))).trans
      (Equiv.sumEmpty _ _)).symm.trans e
  · letI : IsEmpty {f : Option S ⊕ (Fin G.edgeCount × Fin 2) //
        separatingSourceVertex G H (.inl f) = finSumFinEquiv (.inr v)} :=
      ⟨fun x ↦ by
        have h := finSumFinEquiv.injective x.2
        exact Sum.inl_ne_inr h⟩
    let ev := (Equiv.subtypeEquivRight
      (p := fun f : Option T ⊕ (Fin H.edgeCount × Fin 2) ↦
        separatingSourceVertex G H (.inr f) = finSumFinEquiv (.inr v))
      (q := fun f ↦ Sum.elim H.legVertex (fun p ↦ H.endpoint p.1 p.2) f = v)
      (fun f ↦ by
      simp only [separatingSourceVertex, Sum.elim_inr, Equiv.apply_eq_iff_eq,
        Sum.inr.injEq])).trans Equiv.subtypeSum
    exact ((Equiv.subtypeSum.trans ((Equiv.refl _).sumCongr ev)).trans
      (Equiv.emptySum _ _)).symm.trans e

/-- Join two connected stable components by their distinguished markings. -/
def separating (G : StableGraphCode (Option S)) (H : StableGraphCode (Option T)) :
    StableGraphCode (S ⊕ T) where
  vertexCount := G.vertexCount + H.vertexCount
  edgeCount := G.edgeCount + H.edgeCount + 1
  vertexCount_pos := by have h := G.vertexCount_pos; omega
  legVertex := Sum.elim (fun s ↦ finSumFinEquiv (.inl (G.legVertex (some s))))
    (fun t ↦ finSumFinEquiv (.inr (H.legVertex (some t))))
  endpoint := separatingEndpoint G H
  genus := fun v ↦ Sum.elim G.genus H.genus (finSumFinEquiv.symm v)
  connected := by
    let adj := fun x y ↦ ∃ e, (separatingEndpoint G H e 0 = x ∧
      separatingEndpoint G H e 1 = y) ∨ (separatingEndpoint G H e 1 = x ∧
      separatingEndpoint G H e 0 = y)
    have hl : ∀ v w, Relation.ReflTransGen adj
        (finSumFinEquiv (.inl v)) (finSumFinEquiv (.inl w)) := by
      intro v w
      induction G.connected v w with
      | refl => exact .refl
      | tail _ hw ih =>
        apply ih.tail
        obtain ⟨edge, h⟩ := hw
        refine ⟨(finSumFinEquiv (.inl edge)).castSucc, ?_⟩
        simpa only [separatingEndpoint, Fin.lastCases_castSucc,
          Equiv.symm_apply_apply, Sum.elim_inl, Equiv.apply_eq_iff_eq, Sum.inl.injEq] using h
    have hr : ∀ v w, Relation.ReflTransGen adj
        (finSumFinEquiv (.inr v)) (finSumFinEquiv (.inr w)) := by
      intro v w
      induction H.connected v w with
      | refl => exact .refl
      | tail _ hw ih =>
        apply ih.tail
        obtain ⟨edge, h⟩ := hw
        refine ⟨(finSumFinEquiv (.inr edge)).castSucc, ?_⟩
        simpa only [separatingEndpoint, Fin.lastCases_castSucc,
          Equiv.symm_apply_apply, Sum.elim_inr, Equiv.apply_eq_iff_eq, Sum.inr.injEq] using h
    have bridge : adj (finSumFinEquiv (.inl (G.legVertex none)))
        (finSumFinEquiv (.inr (H.legVertex none))) :=
      ⟨Fin.last _, Or.inl ⟨by rw [separatingEndpoint, Fin.lastCases_last]; rfl,
        by rw [separatingEndpoint, Fin.lastCases_last]; rfl⟩⟩
    have back : adj (finSumFinEquiv (.inr (H.legVertex none)))
        (finSumFinEquiv (.inl (G.legVertex none))) :=
      ⟨Fin.last _, Or.inr ⟨by rw [separatingEndpoint, Fin.lastCases_last]; rfl,
        by rw [separatingEndpoint, Fin.lastCases_last]; rfl⟩⟩
    intro v w
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective v
    obtain ⟨w, rfl⟩ := finSumFinEquiv.surjective w
    rcases v with v | v <;> rcases w with w | w
    · exact hl v w
    · exact ((hl v (G.legVertex none)).tail bridge).trans (hr (H.legVertex none) w)
    · exact ((hr v (H.legVertex none)).tail back).trans (hl (G.legVertex none) w)
    · exact hr v w
  stable := by
    intro v
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective v
    rcases v with v | v
    · have hc := Fintype.card_congr (show G.toStableGraph.VertexLabel v ≃ _ from
        (separatingFlagFiberEquiv G H (.inl v)).trans Equiv.subtypeSum)
      rw [StableGraph.card_vertexLabel, Fintype.card_sum] at hc
      simp only [Equiv.symm_apply_apply, Sum.elim_inl]
      have hs := G.stable v
      change 3 ≤ 2 * G.genus v + _ + _
      change Fintype.card {s : Option S // G.legVertex s = v} +
        Fintype.card {p : Fin G.edgeCount × Fin 2 // G.endpoint p.1 p.2 = v} =
          Fintype.card {s : S ⊕ T // Sum.elim
            (fun s ↦ finSumFinEquiv (.inl (G.legVertex (some s))))
            (fun t ↦ finSumFinEquiv (.inr (H.legVertex (some t)))) s =
              finSumFinEquiv (.inl v)} +
          Fintype.card {p : Fin (G.edgeCount + H.edgeCount + 1) × Fin 2 //
            separatingEndpoint G H p.1 p.2 = finSumFinEquiv (.inl v)} at hc
      omega
    · have hc := Fintype.card_congr (show H.toStableGraph.VertexLabel v ≃ _ from
        (separatingFlagFiberEquiv G H (.inr v)).trans Equiv.subtypeSum)
      rw [StableGraph.card_vertexLabel, Fintype.card_sum] at hc
      simp only [Equiv.symm_apply_apply, Sum.elim_inr]
      have hs := H.stable v
      change 3 ≤ 2 * H.genus v + _ + _
      change Fintype.card {s : Option T // H.legVertex s = v} +
        Fintype.card {p : Fin H.edgeCount × Fin 2 // H.endpoint p.1 p.2 = v} =
          Fintype.card {s : S ⊕ T // Sum.elim
            (fun s ↦ finSumFinEquiv (.inl (G.legVertex (some s))))
            (fun t ↦ finSumFinEquiv (.inr (H.legVertex (some t)))) s =
              finSumFinEquiv (.inr v)} +
          Fintype.card {p : Fin (G.edgeCount + H.edgeCount + 1) × Fin 2 //
            separatingEndpoint G H p.1 p.2 = finSumFinEquiv (.inr v)} at hc
      omega

/-- Joining components leaves the sum of their cycle ranks unchanged. -/
theorem separating_firstBetti (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) :
    (G.separating H).firstBetti = G.firstBetti + H.firstBetti := by
  have hg := G.vertexCount_le_edgeCount_add_one
  have hh := H.vertexCount_le_edgeCount_add_one
  change G.edgeCount + H.edgeCount + 1 + 1 - (G.vertexCount + H.vertexCount) =
    (G.edgeCount + 1 - G.vertexCount) + (H.edgeCount + 1 - H.vertexCount)
  omega

/-- The genus of the glued graph is the sum of the two component genera. -/
theorem separating_totalGenus (G : StableGraphCode (Option S))
    (H : StableGraphCode (Option T)) :
    (G.separating H).totalGenus = G.totalGenus + H.totalGenus := by
  have hsum : (∑ v, (G.separating H).genus v) =
      (∑ v, G.genus v) + ∑ v, H.genus v := by
    change (∑ v : Fin (G.vertexCount + H.vertexCount),
      Sum.elim G.genus H.genus (finSumFinEquiv.symm v)) = _
    calc
      _ = ∑ v : Fin G.vertexCount ⊕ Fin H.vertexCount, Sum.elim G.genus H.genus v :=
        (Fintype.sum_equiv finSumFinEquiv (fun v ↦ Sum.elim G.genus H.genus v)
          (fun v ↦ Sum.elim G.genus H.genus (finSumFinEquiv.symm v))
          (fun v ↦ by rw [Equiv.symm_apply_apply])).symm
      _ = _ := Fintype.sum_sum_type _
  rw [totalGenus, hsum, separating_firstBetti, totalGenus, totalGenus]
  omega

/-- Transport two consecutive finite blocks independently. -/
def separatingBlocksEquiv {m n p q : ℕ} (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) :
    Fin (m + n) ≃ Fin (p + q) :=
  (finSumFinEquiv.symm.trans (e.sumCongr f)).trans finSumFinEquiv

/-- Transport in the first block. -/
theorem separatingBlocksEquiv_left {m n p q : ℕ}
    (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) (v : Fin m) :
    separatingBlocksEquiv e f (finSumFinEquiv (.inl v)) = finSumFinEquiv (.inl (e v)) := by
  simp only [separatingBlocksEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]

/-- Transport in the second block. -/
theorem separatingBlocksEquiv_right {m n p q : ℕ}
    (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) (v : Fin n) :
    separatingBlocksEquiv e f (finSumFinEquiv (.inr v)) = finSumFinEquiv (.inr (f v)) := by
  simp only [separatingBlocksEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inr]

/-- Old edge blocks are transported independently and the new edge is fixed. -/
def separatingEdgesEquiv {m n p q : ℕ} (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) :
    Fin (m + n + 1) ≃ Fin (p + q + 1) :=
  (finSuccEquivLast.trans (separatingBlocksEquiv e f).optionCongr).trans finSuccEquivLast.symm

/-- The new edge is fixed under extension of component isomorphisms. -/
theorem separatingEdgesEquiv_last {m n p q : ℕ}
    (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) :
    separatingEdgesEquiv e f (Fin.last (m + n)) = Fin.last (p + q) := by
  simp only [separatingEdgesEquiv, Equiv.trans_apply, finSuccEquivLast_last,
    Equiv.optionCongr_apply, Option.map_none, finSuccEquivLast_symm_none]

/-- First-component edges keep their branch ordering under block transport. -/
theorem separatingEdgesEquiv_left {m n p q : ℕ}
    (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) (edge : Fin m) :
    separatingEdgesEquiv e f (finSumFinEquiv (.inl edge)).castSucc =
      (finSumFinEquiv (.inl (e edge))).castSucc := by
  simp only [separatingEdgesEquiv, Equiv.trans_apply, finSuccEquivLast_castSucc,
    Equiv.optionCongr_apply, Option.map_some, finSuccEquivLast_symm_some,
    separatingBlocksEquiv_left]

/-- Second-component edges remain in their own block. -/
theorem separatingEdgesEquiv_right {m n p q : ℕ}
    (e : Fin m ≃ Fin p) (f : Fin n ≃ Fin q) (edge : Fin n) :
    separatingEdgesEquiv e f (finSumFinEquiv (.inr edge)).castSucc =
      (finSumFinEquiv (.inr (f edge))).castSucc := by
  simp only [separatingEdgesEquiv, Equiv.trans_apply, finSuccEquivLast_castSucc,
    Equiv.optionCongr_apply, Option.map_some, finSuccEquivLast_symm_some,
    separatingBlocksEquiv_right]

/-- Component graph isomorphisms extend to the glued presentation, fixing
the new edge. Additional output automorphisms can also exist. -/
def Iso.separating {G G' : StableGraphCode (Option S)}
    {H H' : StableGraphCode (Option T)} (e : Iso G G') (f : Iso H H') :
    Iso (G.separating H) (G'.separating H') where
  vertexEquiv := separatingBlocksEquiv e.vertexEquiv f.vertexEquiv
  edgeEquiv := separatingEdgesEquiv e.edgeEquiv f.edgeEquiv
  branchEquiv := Fin.lastCases (Equiv.refl (Fin 2))
    (fun edge ↦ Sum.elim e.branchEquiv f.branchEquiv (finSumFinEquiv.symm edge))
  legVertex_comm := by
    intro s
    rcases s with s | t
    · change separatingBlocksEquiv e.vertexEquiv f.vertexEquiv
        (finSumFinEquiv (.inl (G.legVertex (some s)))) = _
      rw [separatingBlocksEquiv_left, e.legVertex_comm]
      rfl
    · change separatingBlocksEquiv e.vertexEquiv f.vertexEquiv
        (finSumFinEquiv (.inr (H.legVertex (some t)))) = _
      rw [separatingBlocksEquiv_right, f.legVertex_comm]
      rfl
  endpoint_comm := by
    intro edge i
    change separatingBlocksEquiv e.vertexEquiv f.vertexEquiv
      (separatingEndpoint G H edge i) =
        separatingEndpoint G' H' (separatingEdgesEquiv e.edgeEquiv f.edgeEquiv edge)
          (Fin.lastCases (motive := fun _ ↦ Fin 2 ≃ Fin 2) (Equiv.refl (Fin 2))
            (fun edge ↦ Sum.elim e.branchEquiv f.branchEquiv (finSumFinEquiv.symm edge)) edge i)
    cases edge using Fin.lastCases with
    | last =>
      rw [separatingEdgesEquiv_last, Fin.lastCases_last, Equiv.refl_apply]
      fin_cases i
      all_goals rw [separatingEndpoint, Fin.lastCases_last,
        separatingEndpoint, Fin.lastCases_last]
      · change separatingBlocksEquiv _ _ (finSumFinEquiv (.inl _)) = _
        rw [separatingBlocksEquiv_left, e.legVertex_comm]
        rfl
      · change separatingBlocksEquiv _ _ (finSumFinEquiv (.inr _)) = _
        rw [separatingBlocksEquiv_right, f.legVertex_comm]
        rfl
    | cast edge =>
      obtain ⟨edge, rfl⟩ := finSumFinEquiv.surjective edge
      rcases edge with edge | edge
      · simp only [separatingEdgesEquiv_left, separatingEndpoint, Fin.lastCases_castSucc,
          Equiv.symm_apply_apply, Sum.elim_inl, separatingBlocksEquiv_left]
        rw [e.endpoint_comm]
      · simp only [separatingEdgesEquiv_right, separatingEndpoint, Fin.lastCases_castSucc,
          Equiv.symm_apply_apply, Sum.elim_inr, separatingBlocksEquiv_right]
        rw [f.endpoint_comm]
  genus_comm := by
    intro v
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective v
    rcases v with v | v
    · change Sum.elim G'.genus H'.genus
        (finSumFinEquiv.symm (separatingBlocksEquiv _ _ (finSumFinEquiv (.inl v)))) = _
      rw [separatingBlocksEquiv_left, Equiv.symm_apply_apply]
      simpa only [StableGraphCode.separating, Equiv.symm_apply_apply, Sum.elim_inl]
        using e.genus_comm v
    · change Sum.elim G'.genus H'.genus
        (finSumFinEquiv.symm (separatingBlocksEquiv _ _ (finSumFinEquiv (.inr v)))) = _
      rw [separatingBlocksEquiv_right, Equiv.symm_apply_apply]
      simpa only [StableGraphCode.separating, Equiv.symm_apply_apply, Sum.elim_inr]
        using f.genus_comm v

end StableGraphCode

namespace DecoratedStableGraph

variable {S T : Type} [Fintype S] [Fintype T]

/-- Raw gluing retains every component decoration and moves the two
distinguished leg powers to the new edge branches. -/
def separating (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T)) : DecoratedStableGraph (S ⊕ T) where
  graph := G.graph.separating H.graph
  kappaPower := fun v ↦ Sum.elim G.kappaPower H.kappaPower (finSumFinEquiv.symm v)
  legPsiPower := Sum.elim (fun s ↦ G.legPsiPower (some s)) (fun t ↦ H.legPsiPower (some t))
  halfEdgePsiPower := Fin.lastCases
    (Fin.cases (G.legPsiPower none) (fun _ ↦ H.legPsiPower none))
    (fun edge i ↦ Sum.elim (fun e ↦ G.halfEdgePsiPower e i)
      (fun e ↦ H.halfEdgePsiPower e i) (finSumFinEquiv.symm edge))

/-- The first component's old half-edge powers are retained. -/
theorem separating_halfEdgePsi_left (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T)) (e : Fin G.graph.edgeCount) (i : Fin 2) :
    (G.separating H).halfEdgePsiPower (finSumFinEquiv (.inl e)).castSucc i =
      G.halfEdgePsiPower e i := by
  simp only [separating, Fin.lastCases_castSucc, Equiv.symm_apply_apply, Sum.elim_inl]

/-- The second component's old half-edge powers are retained. -/
theorem separating_halfEdgePsi_right (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T)) (e : Fin H.graph.edgeCount) (i : Fin 2) :
    (G.separating H).halfEdgePsiPower (finSumFinEquiv (.inr e)).castSucc i =
      H.halfEdgePsiPower e i := by
  simp only [separating, Fin.lastCases_castSucc, Equiv.symm_apply_apply, Sum.elim_inr]

/-- The left distinguished leg power becomes node branch zero. -/
theorem separating_halfEdgePsi_last_zero (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T)) :
    (G.separating H).halfEdgePsiPower (Fin.last (G.graph.edgeCount + H.graph.edgeCount)) 0 =
      G.legPsiPower none := by
  change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ) _ _ (Fin.last _) 0 = _
  rw [Fin.lastCases_last]
  rfl

/-- The right distinguished leg power becomes node branch one. -/
theorem separating_halfEdgePsi_last_one (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T)) :
    (G.separating H).halfEdgePsiPower (Fin.last (G.graph.edgeCount + H.graph.edgeCount)) 1 =
      H.legPsiPower none := by
  change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ) _ _ (Fin.last _) 1 = _
  rw [Fin.lastCases_last]
  rfl

/-- Only the new edge adds codimension; moving the two node powers does
not change their contribution. -/
theorem separating_codimension (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T)) :
    (G.separating H).codimension = G.codimension + H.codimension + 1 := by
  have hk : (G.separating H).kappaCodimension = G.kappaCodimension + H.kappaCodimension := by
    change (∑ v : Fin (G.graph.vertexCount + H.graph.vertexCount),
      (Sum.elim G.kappaPower H.kappaPower (finSumFinEquiv.symm v)).sum
        (fun i power ↦ (i : ℕ) * power)) = _
    calc
      _ = ∑ v : Fin G.graph.vertexCount ⊕ Fin H.graph.vertexCount,
          (Sum.elim G.kappaPower H.kappaPower v).sum (fun i power ↦ (i : ℕ) * power) :=
        (Fintype.sum_equiv finSumFinEquiv _ _
          (fun v ↦ by rw [Equiv.symm_apply_apply])).symm
      _ = _ := by rw [Fintype.sum_sum_type]; rfl
  have hi : (G.separating H).halfEdgePsiCodimension =
      G.halfEdgePsiCodimension + H.halfEdgePsiCodimension +
        G.legPsiPower none + H.legPsiPower none := by
    change (∑ e : Fin (G.graph.edgeCount + H.graph.edgeCount + 1), ∑ i : Fin 2,
      Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ)
        (Fin.cases (G.legPsiPower none) (fun _ ↦ H.legPsiPower none))
        (fun edge i ↦ Sum.elim (fun e ↦ G.halfEdgePsiPower e i)
          (fun e ↦ H.halfEdgePsiPower e i) (finSumFinEquiv.symm edge)) e i) = _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have ho : (∑ e : Fin (G.graph.edgeCount + H.graph.edgeCount), ∑ i,
        Sum.elim (fun e ↦ G.halfEdgePsiPower e i)
          (fun e ↦ H.halfEdgePsiPower e i) (finSumFinEquiv.symm e)) =
        G.halfEdgePsiCodimension + H.halfEdgePsiCodimension := by
      calc
        _ = ∑ e : Fin G.graph.edgeCount ⊕ Fin H.graph.edgeCount, ∑ i,
            Sum.elim (fun e ↦ G.halfEdgePsiPower e i) (fun e ↦ H.halfEdgePsiPower e i) e :=
          (Fintype.sum_equiv finSumFinEquiv _ _
            (fun e ↦ by rw [Equiv.symm_apply_apply])).symm
        _ = _ := by rw [Fintype.sum_sum_type]; rfl
    rw [ho, Fin.sum_univ_two]
    change G.halfEdgePsiCodimension + H.halfEdgePsiCodimension +
      (G.legPsiPower none + H.legPsiPower none) = _
    omega
  rw [codimension, hk, hi]
  change G.graph.edgeCount + H.graph.edgeCount + 1 +
    (G.kappaCodimension + H.kappaCodimension) +
      (∑ s : S ⊕ T, Sum.elim (fun s ↦ G.legPsiPower (some s))
        (fun t ↦ H.legPsiPower (some t)) s) + _ = _
  unfold codimension legPsiCodimension
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_option]
  simp only [Sum.elim_inl, Sum.elim_inr]
  omega

/-- Independent component isomorphisms preserve all glued decorations. -/
def Iso.separating {G G' : DecoratedStableGraph (Option S)}
    {H H' : DecoratedStableGraph (Option T)} (e : Iso G G') (f : Iso H H') :
    Iso (G.separating H) (G'.separating H') where
  graphIso := e.graphIso.separating f.graphIso
  kappaPower_comm := by
    intro v i
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective v
    rcases v with v | v
    · change Sum.elim G'.kappaPower H'.kappaPower
        (finSumFinEquiv.symm (StableGraphCode.separatingBlocksEquiv _ _
          (finSumFinEquiv (.inl v)))) i = _
      rw [StableGraphCode.separatingBlocksEquiv_left, Equiv.symm_apply_apply]
      simpa only [DecoratedStableGraph.separating, Equiv.symm_apply_apply, Sum.elim_inl]
        using e.kappaPower_comm v i
    · change Sum.elim G'.kappaPower H'.kappaPower
        (finSumFinEquiv.symm (StableGraphCode.separatingBlocksEquiv _ _
          (finSumFinEquiv (.inr v)))) i = _
      rw [StableGraphCode.separatingBlocksEquiv_right, Equiv.symm_apply_apply]
      simpa only [DecoratedStableGraph.separating, Equiv.symm_apply_apply, Sum.elim_inr]
        using f.kappaPower_comm v i
  legPsiPower_comm := by
    intro s
    rcases s with s | t
    · exact e.legPsiPower_comm (some s)
    · exact f.legPsiPower_comm (some t)
  halfEdgePsiPower_comm := by
    intro edge i
    change (G'.separating H').halfEdgePsiPower
      (StableGraphCode.separatingEdgesEquiv e.graphIso.edgeEquiv f.graphIso.edgeEquiv edge)
      (Fin.lastCases (motive := fun _ ↦ Fin 2 ≃ Fin 2) (Equiv.refl (Fin 2))
        (fun edge ↦ Sum.elim e.graphIso.branchEquiv f.graphIso.branchEquiv
          (finSumFinEquiv.symm edge)) edge i) = _
    cases edge using Fin.lastCases with
    | last =>
      rw [StableGraphCode.separatingEdgesEquiv_last, Fin.lastCases_last, Equiv.refl_apply]
      fin_cases i
      all_goals change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ) _ _ (Fin.last _) _ = _
      all_goals rw [Fin.lastCases_last]
      · simp only [DecoratedStableGraph.separating, Fin.lastCases_last]
        change G'.legPsiPower none = G.legPsiPower none
        exact e.legPsiPower_comm none
      · simp only [DecoratedStableGraph.separating, Fin.lastCases_last]
        change H'.legPsiPower none = H.legPsiPower none
        exact f.legPsiPower_comm none
    | cast edge =>
      obtain ⟨edge, rfl⟩ := finSumFinEquiv.surjective edge
      rcases edge with edge | edge
      · simp only [StableGraphCode.separatingEdgesEquiv_left, separating_halfEdgePsi_left,
          Fin.lastCases_castSucc, Equiv.symm_apply_apply, Sum.elim_inl]
        exact e.halfEdgePsiPower_comm edge i
      · simp only [StableGraphCode.separatingEdgesEquiv_right, separating_halfEdgePsi_right,
          Fin.lastCases_castSucc, Equiv.symm_apply_apply, Sum.elim_inr]
        exact f.halfEdgePsiPower_comm edge i

end DecoratedStableGraph

namespace TautologicalStratum

variable {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-- Raw separating gluing is well-defined on both component isomorphism
classes. The output forgets the distinguished source decomposition. -/
def separating (x : TautologicalStratum g₁ (Option S))
    (y : TautologicalStratum g₂ (Option T)) : TautologicalStratum (g₁ + g₂) (S ⊕ T) :=
  Quotient.map₂ (fun G H ↦ ⟨G.1.separating H.1, by
    rw [DecoratedStableGraph.separating, StableGraphCode.separating_totalGenus, G.2, H.2]⟩)
    (fun _ _ hg _ _ hh ↦ by
      obtain ⟨e⟩ := hg
      obtain ⟨f⟩ := hh
      exact ⟨e.separating f⟩) x y

/-- The quotient operation computes using the actual graph construction. -/
theorem separating_mk (G : DecoratedStableGraph (Option S))
    (H : DecoratedStableGraph (Option T))
    (hG : G.graph.totalGenus = g₁) (hH : H.graph.totalGenus = g₂) :
    (mk G hG).separating (mk H hH) = mk (G.separating H)
      (G.graph.separating_totalGenus H.graph |>.trans (congrArg₂ (· + ·) hG hH)) := rfl

/-- The two component codimensions and new edge contribute additively. -/
theorem separating_codimension (x : TautologicalStratum g₁ (Option S))
    (y : TautologicalStratum g₂ (Option T)) :
    (x.separating y).codimension = x.codimension + y.codimension + 1 := by
  refine Quotient.inductionOn₂ x y ?_
  intro G H
  exact G.1.separating_codimension H.1

/-- Both component vertex sets survive. -/
theorem separating_vertexCount (x : TautologicalStratum g₁ (Option S))
    (y : TautologicalStratum g₂ (Option T)) :
    (x.separating y).vertexCount = x.vertexCount + y.vertexCount := by
  refine Quotient.inductionOn₂ x y ?_
  intro G H
  rfl

/-- Both edge sets survive and the joining edge is added. -/
theorem separating_edgeCount (x : TautologicalStratum g₁ (Option S))
    (y : TautologicalStratum g₂ (Option T)) :
    (x.separating y).edgeCount = x.edgeCount + y.edgeCount + 1 := by
  refine Quotient.inductionOn₂ x y ?_
  intro G H
  rfl

end TautologicalStratum

namespace StrataModule

variable {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]

/-- Bilinear raw pushforward from the two free strata modules. Coefficients
multiply and coincident output classes add, without automorphism factors. -/
noncomputable def separating : StrataModule g₁ (Option S) →ₗ[ℚ]
    StrataModule g₂ (Option T) →ₗ[ℚ] StrataModule (g₁ + g₂) (S ⊕ T) :=
  Finsupp.linearCombination ℚ (fun x ↦ Finsupp.linearCombination ℚ
    (fun y ↦ basis (x.separating y)))

/-- Two individual coefficients multiply under raw gluing. -/
theorem separating_single_single (x : TautologicalStratum g₁ (Option S))
    (y : TautologicalStratum g₂ (Option T)) (a b : ℚ) :
    separating (Finsupp.single x a) (Finsupp.single y b) =
      (a * b) • basis (x.separating y) := by
  rw [separating, Finsupp.linearCombination_single, LinearMap.smul_apply,
    Finsupp.linearCombination_single, smul_smul]

/-- On basis vectors, the bilinear map is the quotient graph operation. -/
theorem separating_basis_basis (x : TautologicalStratum g₁ (Option S))
    (y : TautologicalStratum g₂ (Option T)) :
    separating (basis x) (basis y) = basis (x.separating y) := by
  rw [basis, basis, separating_single_single, one_mul, one_smul]

/-- Homogeneous input combinations glue in the sum of their degrees plus
the codimension of the new edge. -/
theorem separating_mem_degree {d e : ℕ} {r : StrataModule g₁ (Option S)}
    {s : StrataModule g₂ (Option T)} (hr : r ∈ degree d) (hs : s ∈ degree e) :
    separating r s ∈ degree (d + e + 1) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨y, hy, rfl⟩ := hs
      rw [separating_basis_basis, ← hx, ← hy, ← TautologicalStratum.separating_codimension]
      exact basis_mem_degree _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul q a _ ha => rw [map_smul]; exact Submodule.smul_mem _ q ha
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  | smul q a _ ha =>
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ q ha

end StrataModule

end AxiomaticGW
