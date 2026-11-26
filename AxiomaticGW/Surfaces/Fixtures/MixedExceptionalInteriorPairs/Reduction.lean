/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Squares
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Terminals
public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Transfer

/-! # Removing the primitive and constant tails from mixed exceptional pairs

Each calibrated transfer has exactly one square in the full class, with
coefficient one. The other terms vanish on the original ancestor recursion.
The two ordered markings may therefore be evaluated on the same full-class
square whenever they differ only by reversal.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants SurfaceGenusTwoPositiveSquare

/-- The index of the full-class square in the sixteen-element ancestor frame. -/
def fullIndex (j : Fin 32) : Fin 16 :=
  (#[15, 15, 12, 3, 13, 7, 14, 11, 3, 12, 0, 0, 1, 4, 2, 8,
    7, 13, 4, 1, 5, 5, 6, 9, 11, 14, 8, 2, 9, 6, 10, 10] :
    Array (Fin 16))[j.val]'j.isLt

/-- Both orders of the two markings occur for every full-class square. -/
theorem fullIndex_eq_iff (i j : Fin 32) :
    fullIndex i = fullIndex j ↔ (requests i).insertions = (requests j).insertions ∨
      (requests i).insertions = (requests j).insertions.reverse := by
  revert i j
  decide +kernel

theorem fullIndex_fiber_card (k : Fin 16) :
    (Finset.univ.filter (fun j ↦ fullIndex j = k)).card = 2 := by
  fin_cases k <;> decide +kernel

private def fullKey : Fin 44 → Option (Fin 16) :=
  Fin.addCases (m := 28) (n := 16) (Fin.addCases (m := 12) (n := 16) (fun _ ↦ none) some)
    (fun _ ↦ none)

/-- The original numerical ancestor on a full-class marking frame. -/
abbrev fullAncestor (k : Fin 16) := SurfaceGenusTwo.ancestorValue low (squareKey (Fin.natAdd 12 k))

private theorem kept (k : Fin 44) :
    ancestorValueWith boundary (key k) = (fullKey k).elim 0 fullAncestor := by
  change SurfaceGenusTwo.ancestorValue low (key k) = _
  refine Fin.addCases (m := 28) (n := 16) (fun j ↦ ?_) (fun j ↦ ?_) k
  · simp only [key, fullKey, Fin.addCases_left]
    refine Fin.addCases (m := 12) (n := 16) (fun u ↦ ?_) (fun u ↦ ?_) j
    · simp only [Fin.addCases_left, Option.elim_none]
      rw [square_sum (CertifiedComponents.bounded X)]
      simp only [primitive_parts, Finset.sum_const_zero]
    · simp only [Fin.addCases_right, Option.elim_some, fullAncestor]
  · simp only [key, fullKey, Fin.addCases_right, Option.elim_none]
    refine Fin.addCases (m := 6) (n := 10) (fun u ↦ ?_) (fun u ↦ ?_) j
    · simpa only [Fin.addCases_left] using product_values u
    · simpa only [Fin.addCases_right] using low_values u

private def project (t : ℚ × Fin 44) : Option (ℚ × Fin 16) :=
  (fullKey t.2).map (fun k ↦ (t.1, k))

private theorem projected_sum (ts : List (ℚ × Fin 44)) :
    (ts.map (fun t ↦ t.1 * (fullKey t.2).elim 0 fullAncestor)).sum =
      ((ts.filterMap project).map (fun t ↦ t.1 * fullAncestor t.2)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases e : fullKey t.2 <;>
      simp only [List.map_cons, List.sum_cons, e, Option.elim_none, Option.elim_some,
        mul_zero, zero_add, List.filterMap_cons, project, Option.map_none, Option.map_some,
        ih]

/-- The original mixed descendant equals its unique square in the complete curve E₁ + E₂. -/
theorem query_full_square (j : Fin 32) :
    queryValue? 0 (requests j) = some (fullAncestor (fullIndex j)) := by
  rw [query_from_ancestors]
  simp only [kept, projected_sum]
  rw [show (row j).filterMap project = [(1, fullIndex j)] by fin_cases j <;> decide +kernel]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
