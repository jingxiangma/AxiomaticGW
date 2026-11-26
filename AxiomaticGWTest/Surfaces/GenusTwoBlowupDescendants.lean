/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendants

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupDescendants
open AxiomaticGW SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupDescendants

private def key {X : SurfaceTarget} (ins : List (SurfaceInsertion X)) : SurfaceAncestorKey X :=
  ⟨2, 0, ins, by omega⟩

private theorem boundary_table_correct {X : SurfaceTarget} (i : Fin X.blowups)
    (s : State X) (hs : X.effective.energy s.1 ≤ 0) :
    SurfaceGenusTwoBlowupBoundary.value s.1 s.2 = SurfaceGenusTwoBlowupRecursion.values i s := by
  have hb : s.1 = 0 := (X.effective.energy_eq_zero_iff s.1).mp (by omega)
  exact (SurfaceGenusTwoBlowupRecursion.values_boundary i s (by rw [hb, map_zero])).symm

private theorem initial_ancestor {X : SurfaceTarget} (i : Fin X.blowups)
    (ins : List (SurfaceInsertion X)) :
    ancestorValue i (key ins) =
      ancestorValueWith (fun s ↦ SurfaceGenusTwoBlowupBoundary.value s.1 s.2) (key ins) := by
  exact (ancestorValueWith_eq_of_table i 0 _ (boundary_table_correct i) _ rfl
    (by rw [show (key ins).beta = 0 from rfl, map_zero])).symm

private theorem query_from_zero_terms {X : SurfaceTarget} (i : Fin X.blowups)
    (ins : List (SurfaceInsertion X))
    (ht : SurfaceQuery.ancestorTerms (⟨2, 0, ins⟩ : SurfaceQuery X)
      (by simp only [StableArity]; omega) = RationalTerms.term 1 {key ins}) :
    queryValue? i ⟨2, 0, ins⟩ = some (ancestorValue i (key ins)) := by
  rw [queryValue?, if_pos rfl, descendantValue]
  change some (RationalTerms.eval (ancestorValue i)
    (SurfaceQuery.ancestorTerms (⟨2, 0, ins⟩ : SurfaceQuery X) _)) = _
  rw [ht]
  simp only [RationalTerms.eval_term, map_one, Multiset.map_singleton,
    Multiset.prod_singleton, one_mul]

/-- Empty genus-two markings at class zero are accepted and dimension-forced to zero. -/
theorem empty_class_zero (X : SurfaceTarget) (i : Fin X.blowups) :
    queryValue? i ⟨2, 0, []⟩ = some 0 := by
  cases X with
  | plane => exact Fin.elim0 i
  | hirzebruchOne =>
      rw [query_from_zero_terms i [] (by decide +kernel), initial_ancestor i]
      decide +kernel
  | blowupTwo =>
      rw [query_from_zero_terms i [] (by decide +kernel), initial_ancestor i]
      decide +kernel

set_option maxRecDepth 20000 in
/-- The square branch reproduces F1's existing degree-zero value without a descendant oracle. -/
theorem hirzebruch_one_square : queryValue? (X := .hirzebruchOne) 0
    ⟨2, 0, [⟨.unit, 2⟩]⟩ = some (7 / 720) := by
  rw [query_from_zero_terms 0 _ (by decide +kernel), initial_ancestor 0]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The same algorithm retains Bl2P2's distinct degree-zero square value. -/
theorem blowup_two_square : queryValue? (X := .blowupTwo) 1
    ⟨2, 0, [⟨.unit, 2⟩]⟩ = some (49 / 5760) := by
  rw [query_from_zero_terms 1 _ (by decide +kernel), initial_ancestor 1]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The product branch preserves the first exceptional divisor label with its power. -/
theorem first_exceptional_product : queryValue? (X := .blowupTwo) 1
    ⟨2, 0, [⟨.exceptional 0, 1⟩, ⟨.unit, 1⟩]⟩ = some (-1 / 960) := by
  rw [query_from_zero_terms 1 _ (by decide +kernel), initial_ancestor 1]
  decide +kernel

set_option maxRecDepth 20000 in
/-- The other exceptional coordinate is a separate canonical state with the same finite seed. -/
theorem second_exceptional_product : queryValue? (X := .blowupTwo) 0
    ⟨2, 0, [⟨.exceptional 1, 1⟩, ⟨.unit, 1⟩]⟩ = some (-1 / 960) := by
  rw [query_from_zero_terms 0 _ (by decide +kernel), initial_ancestor 0]
  decide +kernel

/-- Non-genus-two requests are rejected before reconstruction. -/
theorem unsupported_genus (X : SurfaceTarget) (i : Fin X.blowups)
    (q : SurfaceQuery X) (hg : q.genus ≠ 2) : queryValue? i q = none := by
  rw [queryValue?, if_neg hg]

/-- Table substitution retains arbitrary high powers and complete effective classes. -/
theorem bounded_table_substitution (X : SurfaceTarget) (i : Fin X.blowups) (bound : ℕ)
    (v : State X → ℚ) (h : ∀ s, X.effective.energy s.1 ≤ bound →
      v s = SurfaceGenusTwoBlowupRecursion.values i s)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hb : X.effective.energy q.beta ≤ bound) :
    ancestorValueWith v q = ancestorValue i q := ancestorValueWith_eq_of_table i bound v h q hg hb

end AxiomaticGWTest.SurfaceGenusTwoBlowupDescendants
