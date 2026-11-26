/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalBenchmark
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalPairs

/-! # Coverage after the twelve ordered double-exceptional string, dilaton and divisor pairs -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDoubleExceptionalPairBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleExceptionalPairs

/-- The original ordered queries, with indices for the axis, equation, and order. -/
def pairs : Finset (SurfaceQuery .blowupTwo) :=
  Finset.univ.image (fun t : Fin 2 × Fin 3 × Bool ↦ request t.1 t.2.1 t.2.2)

/-- The cumulative verified suite on the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  BlowupDoubleExceptionalBenchmark.twoBlowups ∪ pairs

/-- Both axes and both marking orders survive in each of the three equations. -/
theorem card_pairs : pairs.card = 12 := by decide +kernel

/-- None of these nonzero marked requests occurred in the earlier 908-row suite. -/
theorem disjoint : Disjoint BlowupDoubleExceptionalBenchmark.twoBlowups pairs := by
  apply Finset.disjoint_left.mpr
  intro q h hn
  obtain ⟨⟨i, r, last⟩, _, rfl⟩ := Finset.mem_image.mp hn
  rcases Finset.mem_union.mp h with h | h
  · apply BlowupDoubleExceptionalBenchmark.not_mem_previous _ h
    fin_cases i <;> fin_cases r <;> cases last <;> decide +kernel
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have arity : (request i r last).insertions.length = 2 := by
      fin_cases r <;> cases last <;> rfl
    have hn := congrArg (fun q : SurfaceQuery .blowupTwo ↦ q.insertions.length) hj
    exact (by decide : (1 : ℕ) ≠ 2) (hn.trans arity)

/-- The cumulative suite contains exactly 920 distinct full ordered queries. -/
theorem card_twoBlowups : twoBlowups.card = 920 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDoubleExceptionalBenchmark.card_twoBlowups, card_pairs]

/-- Each counted query is dimension compatible and carries a checked descendant witness. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant 0 q a := by
  rcases Finset.mem_union.mp h with h | h
  · exact BlowupDoubleExceptionalBenchmark.twoBlowups_checked h
  · obtain ⟨⟨i, r, last⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨domain i r last, values r, checked i r last⟩

end AxiomaticGW.GKM.BlowupDoubleExceptionalPairBenchmark
