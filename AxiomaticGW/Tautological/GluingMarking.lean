/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingExpression
public import AxiomaticGW.CohFT.StableCurve

/-!
# Additional markings on undecorated gluing expressions

Adding a marking produces one expression for each original component. Lists
retain coincident graph classes with their multiplicities. New markings never
replace a node flag: the label transports below move the old node flags back
to the distinguished gluing positions before gluing.

This is the combinatorial construction for an undecorated forgetful pullback.
Its cohomological meaning is proved separately from primitive base-change
laws. Pulling back psi/kappa decorations needs additional correction terms.
-/

@[expose] public section

namespace AxiomaticGW

/-- Labels after adjoining `n` ordered markings. The last added label is `none`. -/
abbrev ExtraMarkings : ℕ → Type → Type
  | 0, S => S
  | n + 1, S => Option (ExtraMarkings n S)

/-- The finite structure is the iterated canonical optional-label structure. -/
instance ExtraMarkings.fintype (n : ℕ) (S : Type) [Fintype S] :
    Fintype (ExtraMarkings n S) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype S)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Option (ExtraMarkings n S)))

/-- Enumerate old labels first, followed by added labels in order of addition.
This matches appending new numbered markings in the external graph exchange. -/
def ExtraMarkings.finEquiv : (n m : ℕ) → ExtraMarkings n (Fin m) ≃ Fin (m + n)
  | 0, m => Equiv.refl (Fin m)
  | n + 1, m => (ExtraMarkings.finEquiv n m).optionCongr.trans
      (finSuccEquiv' (Fin.last (m + n))).symm

/-- Every finite addition preserves the original stability condition. -/
theorem StableArity.extraMarkings {g : ℕ} {S : Type} [Fintype S]
    (h : StableArity g S) (n : ℕ) : StableArity g (ExtraMarkings n S) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.option

namespace GluingExpression

/-- These expressions are undecorated, so their codimension is the number of nodes. -/
theorem graph_codimension_eq_edgeCount {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) : x.graph.codimension = x.graph.graph.edgeCount := by
  induction x with
  | fundamental g S h =>
    change (DecoratedStableGraph.oneVertex g S h 0 (fun _ ↦ 0)).codimension = 0
    simp only [DecoratedStableGraph.oneVertex_codimension, Finsupp.sum_zero_index,
      Finset.sum_const_zero, add_zero]
  | relabel e x ih =>
    change (x.graph.relabel e).codimension = x.graph.graph.edgeCount
    rw [DecoratedStableGraph.relabel_codimension, ih]
  | separating x y ihx ihy =>
    change (x.graph.separating y.graph).codimension =
      x.graph.graph.edgeCount + y.graph.graph.edgeCount + 1
    rw [DecoratedStableGraph.separating_codimension, ihx, ihy]
  | nonseparating x ih =>
    change x.graph.nonseparating.codimension = x.graph.graph.edgeCount + 1
    rw [DecoratedStableGraph.nonseparating_codimension, ih]

/-- Add a new external marking at each component, retaining repetitions. -/
def addMarking {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → List (GluingExpression g (Option S))
  | @fundamental g S _ h => [fundamental g (Option S) h.option]
  | @relabel _ _ _ _ _ e x => x.addMarking.map (relabel e.optionCongr)
  | @separating _ _ S T _ _ x y =>
      (x.addMarking.map fun z ↦
        ((z.relabel (swapDoubleOption S)).separating y).relabel (optionSumEquivLeft S T).symm) ++
      (y.addMarking.map fun z ↦
        (x.separating (z.relabel (swapDoubleOption T))).relabel (optionSumEquivRight S T).symm)
  | @nonseparating _ S _ x =>
      x.addMarking.map fun z ↦ (z.relabel (forgetNonseparatingEquiv S).symm).nonseparating

/-- The list contains one placement per vertex, not one per isomorphism class. -/
theorem length_addMarking {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    x.addMarking.length = x.graph.graph.vertexCount := by
  induction x with
  | fundamental g S h => rfl
  | relabel e x ih =>
    change (x.addMarking.map _).length = x.graph.graph.vertexCount
    rw [List.length_map, ih]
  | separating x y ihx ihy =>
    change (x.addMarking.map _ ++ y.addMarking.map _).length =
      x.graph.graph.vertexCount + y.graph.graph.vertexCount
    rw [List.length_append, List.length_map, List.length_map, ihx, ihy]
  | nonseparating x ih =>
    change (x.addMarking.map _).length = x.graph.graph.vertexCount
    rw [List.length_map, ih]

/-- A placement changes no component count. -/
theorem addMarking_vertexCount {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (z : GluingExpression g (Option S))
    (hz : z ∈ x.addMarking) : z.graph.graph.vertexCount = x.graph.graph.vertexCount := by
  induction x with
  | fundamental g S h =>
    simp only [addMarking, List.mem_singleton] at hz
    subst z
    rfl
  | relabel e x ih =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact ih y hy
  | separating x y ihx ihy =>
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact congrArg (· + y.graph.graph.vertexCount) (ihx w hw)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact congrArg (x.graph.graph.vertexCount + ·) (ihy w hw)
  | nonseparating x ih =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact ih y hy

/-- A placement changes no internal edge count. -/
theorem addMarking_edgeCount {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (z : GluingExpression g (Option S))
    (hz : z ∈ x.addMarking) : z.graph.graph.edgeCount = x.graph.graph.edgeCount := by
  induction x with
  | fundamental g S h =>
    simp only [addMarking, List.mem_singleton] at hz
    subst z
    rfl
  | relabel e x ih =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact ih y hy
  | separating x y ihx ihy =>
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact congrArg (fun n ↦ n + y.graph.graph.edgeCount + 1) (ihx w hw)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact congrArg (fun n ↦ x.graph.graph.edgeCount + n + 1) (ihy w hw)
  | nonseparating x ih =>
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact congrArg (· + 1) (ih y hy)

/-- Iterate the same operation for any finite number of ordered new labels. -/
def addMarkings {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) :
    (n : ℕ) → List (GluingExpression g (ExtraMarkings n S))
  | 0 => [x]
  | n + 1 => (x.addMarkings n).flatMap addMarking

/-- Iterated placements still have exactly the original vertices. -/
theorem addMarkings_vertexCount {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (n : ℕ) (z : GluingExpression g (ExtraMarkings n S))
    (hz : z ∈ x.addMarkings n) : z.graph.graph.vertexCount = x.graph.graph.vertexCount := by
  induction n with
  | zero =>
    simp only [addMarkings, List.mem_singleton] at hz
    subst z
    rfl
  | succ n ih =>
    obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hz
    exact (y.addMarking_vertexCount z hzy).trans (ih y hy)

/-- There is one term per assignment of the ordered new labels to vertices. -/
theorem length_addMarkings {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (n : ℕ) :
    (x.addMarkings n).length = x.graph.graph.vertexCount ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [addMarkings, List.length_flatMap]
    have heq : ((x.addMarkings n).map fun z ↦ z.addMarking.length) =
        (x.addMarkings n).map (fun _ ↦ x.graph.graph.vertexCount) := by
      apply List.map_congr_left
      intro z hz
      rw [length_addMarking, x.addMarkings_vertexCount n z hz]
    rw [heq, List.map_const', List.sum_replicate_nat, ih, pow_succ]

/-- Iteration retains every original node. -/
theorem addMarkings_edgeCount {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (n : ℕ) (z : GluingExpression g (ExtraMarkings n S))
    (hz : z ∈ x.addMarkings n) : z.graph.graph.edgeCount = x.graph.graph.edgeCount := by
  induction n with
  | zero =>
    simp only [addMarkings, List.mem_singleton] at hz
    subst z
    rfl
  | succ n ih =>
    obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hz
    exact (y.addMarking_edgeCount z hzy).trans (ih y hy)

/-- The induced raw stratum placements have the original codimension. -/
theorem addMarkings_codimension {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (n : ℕ) (z : GluingExpression g (ExtraMarkings n S))
    (hz : z ∈ x.addMarkings n) : z.stratum.codimension = x.stratum.codimension := by
  change z.graph.codimension = x.graph.codimension
  rw [z.graph_codimension_eq_edgeCount, x.graph_codimension_eq_edgeCount,
    x.addMarkings_edgeCount n z hz]

end GluingExpression

end AxiomaticGW
