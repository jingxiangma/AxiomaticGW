/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalPairBenchmark
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalSingletons

/-! # Coverage of the complete double-exceptional basis-singleton frame on Bl₂ -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDoubleExceptionalSingletonBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleExceptionalSingletons

/-- Three basis states at each axis absent from the preceding suite. -/
def newLabel (i : Fin 2) : Fin 3 → SurfaceBasisLabel .blowupTwo :=
  ![.unit, .hyperplane, .exceptional i.rev]

/-- Six additional original queries, distinct by curve coordinate or marked state. -/
def additional : Finset (SurfaceQuery .blowupTwo) :=
  Finset.univ.image (fun p : Fin 2 × Fin 3 ↦ request p.1 (newLabel p.1 p.2))

/-- The complete ten-row frame, including the earlier own-divisor and point singletons. -/
def singletons : Finset (SurfaceQuery .blowupTwo) :=
  Finset.univ.image (fun p : Fin 2 × SurfaceBasisLabel .blowupTwo ↦ request p.1 p.2)

/-- Cumulative bounded coverage on the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  BlowupDoubleExceptionalPairBenchmark.twoBlowups ∪ additional

private theorem mem_additional (i : Fin 2) (r : Fin 3) :
    request i (newLabel i r) ∈ additional :=
  Finset.mem_image.mpr ⟨(i, r), Finset.mem_univ _, rfl⟩

/-- The six newly added queries belong to none of the earlier numerical and support frames. -/
theorem disjoint : Disjoint BlowupDoubleExceptionalPairBenchmark.twoBlowups additional := by
  apply Finset.disjoint_left.mpr
  intro q h hn
  obtain ⟨⟨i, r⟩, _, rfl⟩ := Finset.mem_image.mp hn
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · apply BlowupDoubleExceptionalBenchmark.not_mem_previous _ h
      fin_cases i <;> fin_cases r <;> decide +kernel
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      have diff : ∀ j : Fin 2, BlowupTwoDoubleExceptionalDivisor.request j ≠
          request i (newLabel i r) := by fin_cases i <;> fin_cases r <;> decide +kernel
      exact diff j hj
  · obtain ⟨⟨j, s, last⟩, _, he⟩ := Finset.mem_image.mp h
    have ar : (BlowupTwoDoubleExceptionalPairs.request j s last).insertions.length = 2 := by
      fin_cases s <;> cases last <;> rfl
    have hn := congrArg (fun q : SurfaceQuery .blowupTwo ↦ q.insertions.length) he
    exact (by decide : (2 : ℕ) ≠ 1) (ar.symm.trans hn)

/-- There are 926 distinct original ordered Bl₂ queries in the cumulative suite. -/
theorem card_twoBlowups : twoBlowups.card = 926 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDoubleExceptionalPairBenchmark.card_twoBlowups]
  decide +kernel

private theorem old_point (i : Fin 2) :
    request i .point ∈ BlowupDoubleExceptionalPairBenchmark.twoBlowups := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  let j : Fin 514 := ![268, 20] i
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by fin_cases i <;> decide +kernel⟩,
    by fin_cases i <;> decide +kernel⟩

private theorem old_divisor (i : Fin 2) :
    request i (.exceptional i) ∈ BlowupDoubleExceptionalPairBenchmark.twoBlowups := by
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

-- Membership in the previous large suite is now used solely through its proved interface.
attribute [local irreducible] BlowupDoubleExceptionalPairBenchmark.twoBlowups

/-- The enlarged suite contains every original basis singleton on both axes. -/
theorem mem_twoBlowups (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) :
    request i a ∈ twoBlowups := by
  rw [twoBlowups, Finset.mem_union]
  cases a with
  | unit => exact Or.inr (mem_additional i 0)
  | hyperplane => exact Or.inr (mem_additional i 1)
  | point => exact Or.inl (old_point i)
  | exceptional j =>
    by_cases h : i = j
    · subst j
      exact Or.inl (old_divisor i)
    · have hj : j = i.rev := by fin_cases i <;> fin_cases j <;> first | rfl | contradiction
      rw [hj]
      exact Or.inr (mem_additional i 2)

/-- Four of the ten full singleton queries already occurred in the former 920-row suite. -/
theorem overlap : (BlowupDoubleExceptionalPairBenchmark.twoBlowups ∩ singletons).card = 4 := by
  have hu : BlowupDoubleExceptionalPairBenchmark.twoBlowups ∪ singletons = twoBlowups := by
    ext q
    rw [twoBlowups, Finset.mem_union, Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨⟨i, a⟩, _, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_union.mp (mem_twoBlowups i a)
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨⟨i, r⟩, _, rfl⟩ := Finset.mem_image.mp h
        exact Or.inr (Finset.mem_image.mpr ⟨(i, newLabel i r), Finset.mem_univ _, rfl⟩)
  have ht : singletons.card = 10 := by decide +kernel
  have hc := Finset.card_union_add_card_inter
    BlowupDoubleExceptionalPairBenchmark.twoBlowups singletons
  rw [hu, card_twoBlowups, BlowupDoubleExceptionalPairBenchmark.card_twoBlowups, ht] at hc
  omega

/-- Every counted request has its own ordered arithmetic witness. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant 0 q a := by
  rcases Finset.mem_union.mp h with h | h
  · exact BlowupDoubleExceptionalPairBenchmark.twoBlowups_checked h
  · obtain ⟨⟨i, r⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨domain i _, value i _, checked i _⟩

end AxiomaticGW.GKM.BlowupDoubleExceptionalSingletonBenchmark
