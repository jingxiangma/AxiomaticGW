/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedGluingMarking

/-!
# Degree and genus of the signed decorated pullback

New correction edges replace exactly one cotangent power. Thus every output
has the same total codimension, and added rational tails never increase the
largest component genus. These statements concern the actual constructed
graphs, independently of any cohomology realization.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- An original component cannot have larger genus than the whole graph. -/
theorem maxComponentGenus_le {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) : x.maxComponentGenus ≤ g := by
  induction x with
  | fundamental g S h => exact le_rfl
  | relabel e x ih => exact ih
  | separating x y ihx ihy =>
    change max x.maxComponentGenus y.maxComponentGenus ≤ _
    exact max_le (by omega) (by omega)
  | nonseparating x ih => exact ih.trans (Nat.le_succ _)

/-- Added tails have genus zero and no original component is removed. -/
theorem addCotangentMarking_maxComponentGenus {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (z : ℤ × CotangentTerm g (Option S)) (hz : z ∈ x.addCotangentMarking d l) :
    z.2.expression.maxComponentGenus = x.maxComponentGenus := by
  induction x with
  | fundamental g S h =>
    letI := l
    simp only [addCotangentMarking, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_map, Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | ⟨s, _, rfl⟩
    · rfl
    · simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
        CotangentTerm.fundamental, maxComponentGenus, max_eq_left (Nat.zero_le g)]
  | relabel e x ih =>
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    exact ih d l w hw
  | separating x y ihx ihy =>
    rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      exact congrArg (fun k ↦ max k y.maxComponentGenus) (ihx d.1 l.1 w hw)
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      exact congrArg (max x.maxComponentGenus) (ihy d.2 l.2 w hw)
  | nonseparating x ih =>
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    exact ih d l w hw

/-- Every signed iterated pullback retains the original largest component genus. -/
theorem CotangentTerm.addMarkings_maxComponentGenus {g : ℕ} {S : Type} [Fintype S]
    (x : CotangentTerm g S) (n : ℕ)
    (z : ℤ × CotangentTerm g (ExtraMarkings n S)) (hz : z ∈ x.addMarkings n) :
    z.2.expression.maxComponentGenus = x.expression.maxComponentGenus := by
  induction n with
  | zero =>
    simp only [CotangentTerm.addMarkings, Multiset.mem_singleton] at hz
    subst z
    rfl
  | succ n ih =>
    obtain ⟨t, ht, hscaled⟩ := Multiset.mem_bind.mp hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hscaled
    exact (t.2.expression.addCotangentMarking_maxComponentGenus
      t.2.decoration t.2.labels w hw).trans (ih t ht)

/-- A correction replaces one cotangent power by one node. -/
theorem CotangentTerm.tail_codimension {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (d : S → ℕ) (s : S) (hd : d s ≠ 0) :
    ((CotangentTerm.tail h d s).expression.decoratedGraph
      (CotangentTerm.tail h d s).decoration).codimension = ∑ i, d i := by
  simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
    CotangentTerm.fundamental, decoratedGraph, DecoratedStableGraph.relabel_codimension,
    DecoratedStableGraph.separating_codimension, DecoratedStableGraph.oneVertex_codimension,
    Finsupp.sum_zero_index, Finset.sum_const_zero, zero_add, add_zero]
  rw [Finset.sum_update_of_mem (Finset.mem_univ s) d, Finset.sdiff_singleton_eq_erase]
  have he := Finset.add_sum_erase Finset.univ d (Finset.mem_univ s)
  omega

/-- Every output has the original codimension and no larger component genus. -/
theorem addCotangentMarking_bounds {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (z : ℤ × CotangentTerm g (Option S)) (hz : z ∈ x.addCotangentMarking d l) :
    (z.2.expression.decoratedGraph z.2.decoration).codimension = (x.decoratedGraph d).codimension ∧
      z.2.expression.maxComponentGenus ≤ x.maxComponentGenus := by
  induction x with
  | fundamental g S h =>
    letI := l
    simp only [addCotangentMarking, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_map, Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | ⟨s, hs, rfl⟩
    · constructor
      · simp only [CotangentTerm.fundamental, decoratedGraph,
          DecoratedStableGraph.oneVertex_codimension, Fintype.sum_option, Option.elim_none,
          Option.elim_some, zero_add]
      · exact le_rfl
    · constructor
      · rw [CotangentTerm.tail_codimension h d s hs]
        simp only [decoratedGraph, DecoratedStableGraph.oneVertex_codimension,
          Finsupp.sum_zero_index, zero_add]
      · simp only [CotangentTerm.tail, CotangentTerm.relabel, CotangentTerm.separating,
          CotangentTerm.fundamental, maxComponentGenus, max_eq_left (Nat.zero_le g), le_refl]
  | relabel e x ih =>
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    obtain ⟨hc, hg⟩ := ih d l w hw
    constructor
    · simpa only [CotangentTerm.relabel, decoratedGraph,
        DecoratedStableGraph.relabel_codimension] using hc
    · exact hg
  | separating x y ihx ihy =>
    rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨hc, hg⟩ := ihx d.1 l.1 w hw
      constructor
      · simp only [CotangentTerm.relabel, CotangentTerm.separating, decoratedGraph,
          DecoratedStableGraph.relabel_codimension, DecoratedStableGraph.separating_codimension, hc]
      · exact max_le_max_right y.maxComponentGenus hg
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨hc, hg⟩ := ihy d.2 l.2 w hw
      constructor
      · simp only [CotangentTerm.relabel, CotangentTerm.separating, decoratedGraph,
          DecoratedStableGraph.relabel_codimension, DecoratedStableGraph.separating_codimension, hc]
      · exact max_le_max_left x.maxComponentGenus hg
  | nonseparating x ih =>
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    obtain ⟨hc, hg⟩ := ih d l w hw
    constructor
    · simp only [CotangentTerm.nonseparating, CotangentTerm.relabel, decoratedGraph,
        DecoratedStableGraph.nonseparating_codimension,
        DecoratedStableGraph.relabel_codimension, hc]
    · exact hg

/-- Iteration preserves the graph degree and the component-genus bound. -/
theorem CotangentTerm.addMarkings_bounds {g : ℕ} {S : Type} [Fintype S]
    (x : CotangentTerm g S) (n : ℕ)
    (z : ℤ × CotangentTerm g (ExtraMarkings n S)) (hz : z ∈ x.addMarkings n) :
    (z.2.expression.decoratedGraph z.2.decoration).codimension =
      (x.expression.decoratedGraph x.decoration).codimension ∧
        z.2.expression.maxComponentGenus ≤ x.expression.maxComponentGenus := by
  induction n with
  | zero =>
    simp only [CotangentTerm.addMarkings, Multiset.mem_singleton] at hz
    subst z
    exact ⟨rfl, le_rfl⟩
  | succ n ih =>
    obtain ⟨t, ht, hscaled⟩ := Multiset.mem_bind.mp hz
    obtain ⟨w, hplacement, rfl⟩ := Multiset.mem_map.mp hscaled
    obtain ⟨hc, hg⟩ := t.2.expression.addCotangentMarking_bounds
      t.2.decoration t.2.labels w hplacement
    obtain ⟨hc', hg'⟩ := ih t ht
    exact ⟨hc.trans hc', hg.trans hg'⟩

end AxiomaticGW.GluingExpression
