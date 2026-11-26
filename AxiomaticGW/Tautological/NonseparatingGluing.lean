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
# Nonseparating gluing of decorated strata

The markings `none` and `some none` become branches zero and one of a new
last edge. Every old flag, vertex genus, and kappa decoration is retained.
In particular, gluing at one vertex produces a loop with two flags.

This is the raw graph pushforward convention: coefficients are not divided
by an automorphism order. Gluing can create new automorphisms, and the map
on isomorphism classes need not be injective. Its geometric interpretation
requires a compatible proper pushforward, supplied separately.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace StableGraphCode

variable {S : Type} [Fintype S]

/-- The flag bijection replaces the two distinguished legs by the two
branches of the new last edge; all other labels remain fixed. -/
def nonseparatingFlagsEquiv (S : Type) (n : ℕ) :
    Option (Option S) ⊕ (Fin n × Fin 2) ≃ S ⊕ (Fin (n + 1) × Fin 2) where
  toFun
    | .inl none => .inr (Fin.last n, 0)
    | .inl (some none) => .inr (Fin.last n, 1)
    | .inl (some (some s)) => .inl s
    | .inr (e, i) => .inr (e.castSucc, i)
  invFun
    | .inl s => .inl (some (some s))
    | .inr (e, i) => Fin.lastCases
        (.inl ((doubleOptionEquiv S).symm (.inr i)))
        (fun e ↦ .inr (e, i)) e
  left_inv x := by
    rcases x with (_ | (_ | s)) | ⟨e, i⟩
    all_goals simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> rfl
  right_inv x := by
    rcases x with s | ⟨e, i⟩
    · rfl
    · cases e using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        fin_cases i <;> rfl
      | cast e => simp only [Fin.lastCases_castSucc]

/-- Append the edge whose ordered endpoints are the two node markings. -/
def nonseparatingEndpoint (G : StableGraphCode (Option (Option S))) :
    Fin (G.edgeCount + 1) → Fin 2 → Fin G.vertexCount :=
  Fin.lastCases (fun i ↦ G.legVertex ((doubleOptionEquiv S).symm (.inr i))) G.endpoint

/-- The flag bijection restricted to a vertex, before constructing the
glued graph. Its cardinal equality supplies the stability proof. -/
def nonseparatingFlagFiberEquiv
    (G : StableGraphCode (Option (Option S))) (v : Fin G.vertexCount) :
    G.toStableGraph.VertexLabel v ≃
      {s : S // G.legVertex (some (some s)) = v} ⊕
      {p : Fin (G.edgeCount + 1) × Fin 2 // nonseparatingEndpoint G p.1 p.2 = v} := by
  let oldVertex : Option (Option S) ⊕ (Fin G.edgeCount × Fin 2) → Fin G.vertexCount :=
    Sum.elim G.legVertex (fun p ↦ G.endpoint p.1 p.2)
  let newVertex : S ⊕ (Fin (G.edgeCount + 1) × Fin 2) → Fin G.vertexCount :=
    Sum.elim (fun s ↦ G.legVertex (some (some s)))
      (fun p ↦ nonseparatingEndpoint G p.1 p.2)
  have hflag : ∀ x, oldVertex x =
      newVertex (nonseparatingFlagsEquiv S G.edgeCount x) := by
    intro x
    rcases x with (_ | (_ | s)) | ⟨e, i⟩
    · change _ = nonseparatingEndpoint G (Fin.last G.edgeCount) 0
      rw [nonseparatingEndpoint, Fin.lastCases_last]
      rfl
    · change _ = nonseparatingEndpoint G (Fin.last G.edgeCount) 1
      rw [nonseparatingEndpoint, Fin.lastCases_last]
      rfl
    · rfl
    · change _ = nonseparatingEndpoint G e.castSucc i
      rw [nonseparatingEndpoint, Fin.lastCases_castSucc]
      rfl
  let e := (nonseparatingFlagsEquiv S G.edgeCount).subtypeEquiv
    (p := fun x ↦ oldVertex x = v) (q := fun x ↦ newVertex x = v)
    (fun x ↦ by rw [hflag x])
  exact Equiv.subtypeSum.symm.trans (e.trans Equiv.subtypeSum)

/-- Join the two distinguished legs of a connected stable graph. The new
edge may be a loop or may join distinct vertices in the same component. -/
def nonseparating (G : StableGraphCode (Option (Option S))) : StableGraphCode S where
  vertexCount := G.vertexCount
  edgeCount := G.edgeCount + 1
  vertexCount_pos := G.vertexCount_pos
  legVertex := fun s ↦ G.legVertex (some (some s))
  endpoint := nonseparatingEndpoint G
  genus := G.genus
  connected := by
    intro v w
    apply Relation.ReflTransGen.mono ?_ v w (G.connected v w)
    intro x y h
    rcases h with ⟨e, h⟩
    refine ⟨e.castSucc, ?_⟩
    simpa only [nonseparatingEndpoint, Fin.lastCases_castSucc] using h
  stable := by
    intro v
    have hcard := Fintype.card_congr (nonseparatingFlagFiberEquiv G v)
    rw [StableGraph.card_vertexLabel, Fintype.card_sum] at hcard
    change Fintype.card {s : Option (Option S) // G.legVertex s = v} +
      Fintype.card {p : Fin G.edgeCount × Fin 2 // G.endpoint p.1 p.2 = v} =
      Fintype.card {s : S // G.legVertex (some (some s)) = v} +
      Fintype.card {p : Fin (G.edgeCount + 1) × Fin 2 //
        nonseparatingEndpoint G p.1 p.2 = v} at hcard
    have h := G.stable v
    change 3 ≤ 2 * G.genus v + _ + _
    omega

/-- Gluing preserves the vertex flags bijectively, including both branches
when the distinguished legs meet the same vertex. -/
def nonseparatingVertexLabelEquiv (G : StableGraphCode (Option (Option S)))
    (v : Fin G.vertexCount) :
    G.toStableGraph.VertexLabel v ≃ G.nonseparating.toStableGraph.VertexLabel v :=
  nonseparatingFlagFiberEquiv G v

/-- Existing edge endpoints are retained in their original order. -/
theorem nonseparating_endpoint_castSucc (G : StableGraphCode (Option (Option S)))
    (e : Fin G.edgeCount) (i : Fin 2) :
    G.nonseparating.endpoint e.castSucc i = G.endpoint e i :=
  congrFun (Fin.lastCases_castSucc (motive := fun _ ↦ Fin 2 → Fin G.vertexCount) e) i

/-- Branch zero of the new edge is the first distinguished marking. -/
theorem nonseparating_endpoint_last_zero (G : StableGraphCode (Option (Option S))) :
    G.nonseparating.endpoint (Fin.last G.edgeCount) 0 = G.legVertex none := by
  change nonseparatingEndpoint G (Fin.last G.edgeCount) 0 = _
  rw [nonseparatingEndpoint, Fin.lastCases_last]
  rfl

/-- Branch one of the new edge is the second distinguished marking. -/
theorem nonseparating_endpoint_last_one (G : StableGraphCode (Option (Option S))) :
    G.nonseparating.endpoint (Fin.last G.edgeCount) 1 = G.legVertex (some none) := by
  change nonseparatingEndpoint G (Fin.last G.edgeCount) 1 = _
  rw [nonseparatingEndpoint, Fin.lastCases_last]
  rfl

/-- The first Betti number rises by one because connectedness gives the
bound needed to avoid truncated subtraction. -/
theorem nonseparating_firstBetti (G : StableGraphCode (Option (Option S))) :
    G.nonseparating.firstBetti = G.firstBetti + 1 := by
  have h := G.vertexCount_le_edgeCount_add_one
  change G.edgeCount + 1 + 1 - G.vertexCount = G.edgeCount + 1 - G.vertexCount + 1
  omega

/-- The arithmetic genus rises by one, without changing any vertex genus. -/
theorem nonseparating_totalGenus (G : StableGraphCode (Option (Option S))) :
    G.nonseparating.totalGenus = G.totalGenus + 1 := by
  change (∑ v, G.genus v) + G.nonseparating.firstBetti = _
  rw [G.nonseparating_firstBetti, totalGenus, Nat.add_assoc]

/-- A label-preserving isomorphism extends by fixing the newly appended
edge and its ordered branches. Other output isomorphisms can also exist. -/
def Iso.nonseparating {G H : StableGraphCode (Option (Option S))} (e : Iso G H) :
    Iso G.nonseparating H.nonseparating where
  vertexEquiv := e.vertexEquiv
  edgeEquiv := (finSuccEquivLast.trans e.edgeEquiv.optionCongr).trans finSuccEquivLast.symm
  branchEquiv := Fin.lastCases (Equiv.refl (Fin 2)) e.branchEquiv
  legVertex_comm := fun s ↦ e.legVertex_comm (some (some s))
  endpoint_comm := by
    intro edge i
    cases edge using Fin.lastCases with
    | last =>
      change e.vertexEquiv (nonseparatingEndpoint G (Fin.last G.edgeCount) i) =
        nonseparatingEndpoint H
          (((finSuccEquivLast.trans e.edgeEquiv.optionCongr).trans finSuccEquivLast.symm)
            (Fin.last G.edgeCount))
          (Fin.lastCases (motive := fun _ ↦ Fin 2 ≃ Fin 2)
            (Equiv.refl (Fin 2)) e.branchEquiv (Fin.last G.edgeCount) i)
      simp only [Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionCongr_apply,
        Option.map_none, finSuccEquivLast_symm_none, Fin.lastCases_last,
        Equiv.refl_apply, nonseparatingEndpoint]
      exact e.legVertex_comm _
    | cast edge =>
      change e.vertexEquiv (nonseparatingEndpoint G edge.castSucc i) =
        nonseparatingEndpoint H
          (((finSuccEquivLast.trans e.edgeEquiv.optionCongr).trans finSuccEquivLast.symm)
            edge.castSucc)
          (Fin.lastCases (motive := fun _ ↦ Fin 2 ≃ Fin 2)
            (Equiv.refl (Fin 2)) e.branchEquiv edge.castSucc i)
      simp only [Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquivLast_symm_some, Fin.lastCases_castSucc,
        nonseparatingEndpoint]
      exact e.endpoint_comm edge i
  genus_comm := e.genus_comm

end StableGraphCode

namespace DecoratedStableGraph

variable {S : Type} [Fintype S]

/-- Raw nonseparating gluing. The two distinguished psi powers decorate the
new node branches; no decoration or automorphism factor is discarded. -/
def nonseparating (G : DecoratedStableGraph (Option (Option S))) : DecoratedStableGraph S where
  graph := G.graph.nonseparating
  kappaPower := G.kappaPower
  legPsiPower := fun s ↦ G.legPsiPower (some (some s))
  halfEdgePsiPower := Fin.lastCases
    (fun i ↦ G.legPsiPower ((doubleOptionEquiv S).symm (.inr i))) G.halfEdgePsiPower

/-- Old internal psi powers remain on the same old flags. -/
theorem nonseparating_halfEdgePsi_castSucc (G : DecoratedStableGraph (Option (Option S)))
    (e : Fin G.graph.edgeCount) (i : Fin 2) :
    G.nonseparating.halfEdgePsiPower e.castSucc i = G.halfEdgePsiPower e i :=
  congrFun (Fin.lastCases_castSucc (motive := fun _ ↦ Fin 2 → ℕ) e) i

/-- The first node branch carries the first distinguished leg's power. -/
theorem nonseparating_halfEdgePsi_last_zero (G : DecoratedStableGraph (Option (Option S))) :
    G.nonseparating.halfEdgePsiPower (Fin.last G.graph.edgeCount) 0 = G.legPsiPower none := by
  change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ) _ _ (Fin.last G.graph.edgeCount) 0 = _
  rw [Fin.lastCases_last]
  rfl

/-- The second node branch carries the second distinguished leg's power. -/
theorem nonseparating_halfEdgePsi_last_one (G : DecoratedStableGraph (Option (Option S))) :
    G.nonseparating.halfEdgePsiPower (Fin.last G.graph.edgeCount) 1 =
      G.legPsiPower (some none) := by
  change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ) _ _ (Fin.last G.graph.edgeCount) 1 = _
  rw [Fin.lastCases_last]
  rfl

/-- Moving psi powers from legs to node branches preserves their total;
only the newly added edge increases the stratum codimension. -/
theorem nonseparating_codimension (G : DecoratedStableGraph (Option (Option S))) :
    G.nonseparating.codimension = G.codimension + 1 := by
  have hpsi : G.nonseparating.halfEdgePsiCodimension =
      G.halfEdgePsiCodimension + G.legPsiPower none + G.legPsiPower (some none) := by
    change (∑ e : Fin (G.graph.edgeCount + 1), ∑ i : Fin 2,
      Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ)
        (fun i ↦ G.legPsiPower ((doubleOptionEquiv S).symm (.inr i)))
        G.halfEdgePsiPower e i) = _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have hn : (∑ i : Fin 2, G.legPsiPower ((doubleOptionEquiv S).symm (.inr i))) =
        G.legPsiPower none + G.legPsiPower (some none) := by
      rw [Fin.sum_univ_two]
      rfl
    rw [hn]
    exact Nat.add_assoc _ _ _ |>.symm
  rw [codimension, hpsi]
  change G.graph.edgeCount + 1 + G.kappaCodimension +
    (∑ s, G.legPsiPower (some (some s))) +
    (G.halfEdgePsiCodimension + G.legPsiPower none + G.legPsiPower (some none)) = _
  unfold codimension legPsiCodimension
  rw [Fintype.sum_option, Fintype.sum_option]
  omega

/-- Isomorphisms retain every decoration after gluing, including the two
formerly external powers on the new edge. -/
def Iso.nonseparating {G H : DecoratedStableGraph (Option (Option S))} (e : Iso G H) :
    Iso G.nonseparating H.nonseparating where
  graphIso := e.graphIso.nonseparating
  kappaPower_comm := e.kappaPower_comm
  legPsiPower_comm := fun s ↦ e.legPsiPower_comm (some (some s))
  halfEdgePsiPower_comm := by
    intro edge i
    cases edge using Fin.lastCases with
    | last =>
      change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ)
        (fun i ↦ H.legPsiPower ((doubleOptionEquiv S).symm (.inr i))) H.halfEdgePsiPower
        (((finSuccEquivLast.trans e.graphIso.edgeEquiv.optionCongr).trans finSuccEquivLast.symm)
          (Fin.last G.graph.edgeCount))
        (Fin.lastCases (motive := fun _ ↦ Fin 2 ≃ Fin 2)
          (Equiv.refl (Fin 2)) e.graphIso.branchEquiv
          (Fin.last G.graph.edgeCount) i) = _
      simp only [Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionCongr_apply,
        Option.map_none, finSuccEquivLast_symm_none, Fin.lastCases_last, Equiv.refl_apply,
        DecoratedStableGraph.nonseparating]
      exact e.legPsiPower_comm _
    | cast edge =>
      change Fin.lastCases (motive := fun _ ↦ Fin 2 → ℕ)
        (fun i ↦ H.legPsiPower ((doubleOptionEquiv S).symm (.inr i))) H.halfEdgePsiPower
        (((finSuccEquivLast.trans e.graphIso.edgeEquiv.optionCongr).trans finSuccEquivLast.symm)
          edge.castSucc)
        (Fin.lastCases (motive := fun _ ↦ Fin 2 ≃ Fin 2)
          (Equiv.refl (Fin 2)) e.graphIso.branchEquiv edge.castSucc i) = _
      simp only [Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionCongr_apply,
        Option.map_some, finSuccEquivLast_symm_some, Fin.lastCases_castSucc,
        DecoratedStableGraph.nonseparating]
      exact e.halfEdgePsiPower_comm edge i

end DecoratedStableGraph

namespace TautologicalStratum

variable {g : ℕ} {S : Type} [Fintype S]

/-- Raw nonseparating pushforward on decorated graph isomorphism classes. -/
def nonseparating (x : TautologicalStratum g (Option (Option S))) :
    TautologicalStratum (g + 1) S :=
  Quotient.map (fun G ↦ ⟨G.1.nonseparating, by
    rw [DecoratedStableGraph.nonseparating, StableGraphCode.nonseparating_totalGenus, G.2]⟩)
    (fun _ _ h ↦ by obtain ⟨e⟩ := h; exact ⟨e.nonseparating⟩) x

/-- Computation on a presentation uses the actual gluing construction. -/
theorem nonseparating_mk (G : DecoratedStableGraph (Option (Option S)))
    (hG : G.graph.totalGenus = g) :
    (mk G hG).nonseparating = mk G.nonseparating
      (G.graph.nonseparating_totalGenus.trans (congrArg (fun n ↦ n + 1) hG)) := rfl

/-- Each source stratum gains exactly one boundary codimension. -/
theorem nonseparating_codimension (x : TautologicalStratum g (Option (Option S))) :
    x.nonseparating.codimension = x.codimension + 1 := by
  refine Quotient.inductionOn x ?_
  intro G
  exact G.1.nonseparating_codimension

/-- Gluing retains all vertices. -/
theorem nonseparating_vertexCount (x : TautologicalStratum g (Option (Option S))) :
    x.nonseparating.vertexCount = x.vertexCount := by
  refine Quotient.inductionOn x ?_
  intro G
  rfl

/-- Gluing adds one internal edge. -/
theorem nonseparating_edgeCount (x : TautologicalStratum g (Option (Option S))) :
    x.nonseparating.edgeCount = x.edgeCount + 1 := by
  refine Quotient.inductionOn x ?_
  intro G
  rfl

end TautologicalStratum

namespace StrataModule

variable {g : ℕ} {S : Type} [Fintype S]

/-- Rational linear nonseparating pushforward. Source coefficients remain
unchanged; coincident output classes are combined by the free module. -/
noncomputable def nonseparating :
    StrataModule g (Option (Option S)) →ₗ[ℚ] StrataModule (g + 1) S :=
  Finsupp.linearCombination ℚ (fun x ↦ basis x.nonseparating)

/-- A single coefficient is attached to the glued stratum without an
automorphism divisor. -/
theorem nonseparating_single (x : TautologicalStratum g (Option (Option S))) (q : ℚ) :
    nonseparating (Finsupp.single x q) = q • basis x.nonseparating :=
  Finsupp.linearCombination_single _ _ _

/-- Gluing on basis strata agrees with the quotient graph operation. -/
theorem nonseparating_basis (x : TautologicalStratum g (Option (Option S))) :
    nonseparating (basis x) = basis x.nonseparating := by
  rw [basis, nonseparating_single, one_smul]

/-- Homogeneous rational combinations gain exactly one codimension. -/
theorem nonseparating_mem_degree {d : ℕ} {r : StrataModule g (Option (Option S))}
    (hr : r ∈ degree d) : nonseparating r ∈ degree (d + 1) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    rw [nonseparating_basis, ← hx, ← TautologicalStratum.nonseparating_codimension]
    exact basis_mem_degree _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul q a _ ha => rw [map_smul]; exact Submodule.smul_mem _ q ha

/-- Above-dimension classes stay above dimension under the codimension-one
gluing map. Stability gives the exact source/target dimension identity. -/
theorem nonseparating_mem_dimensionRelations (h : StableArity (g + 1) S)
    {r : StrataModule g (Option (Option S))} (hr : r ∈ dimensionRelations) :
    nonseparating r ∈ dimensionRelations := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    rw [nonseparating_basis]
    apply basis_mem_dimensionRelations
    rw [TautologicalStratum.nonseparating_codimension,
      ← StableArity.dimension_nonseparating h]
    omega
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul q a _ ha => rw [map_smul]; exact Submodule.smul_mem _ q ha

end StrataModule

end AxiomaticGW
