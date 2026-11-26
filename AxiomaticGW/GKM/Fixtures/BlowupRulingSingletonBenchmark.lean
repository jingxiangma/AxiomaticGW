/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDoubleLineSingletonBenchmark
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoRulingOneMarking

/-! # Ten new genus-two singleton requests on the two rulings of Bl₂ -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupRulingSingletonBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupTwoRuling

/-- Each ruling has five basis singletons at the required virtual-dimension power. -/
def singletons : Finset (SurfaceQuery .blowupTwo) :=
  Finset.univ.image fun p : Fin 2 × SurfaceBasisLabel .blowupTwo ↦ request p.1 p.2

/-- Cumulative checked requests for the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  BlowupDoubleLineSingletonBenchmark.twoBlowups ∪ singletons

private theorem exclusions (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) : let q := request i a
    (X.effective.energy q.beta ≠ 1 ∧ exceptionalPointQueryValue? q ≠ some 0 ∧
      q.beta ≠ ![1, 1, 0] ∧ zeroDivisorPair? q ≠ some 0) ∧
    q ∉ Finset.univ.image BlowupTwoDoubleExceptionalDivisor.request ∧
    q ∉ BlowupDoubleExceptionalPairBenchmark.pairs ∧
    q ∉ BlowupDoubleExceptionalSingletonBenchmark.additional ∧
    q ∉ BlowupDoubleLineSingletonBenchmark.singletons := by
  revert i a
  decide +kernel

attribute [local irreducible] BlowupDoubleLineSingletonBenchmark.twoBlowups

/-- Both full ruling classes give new requests outside every earlier certified slice. -/
theorem disjoint : Disjoint BlowupDoubleLineSingletonBenchmark.twoBlowups singletons := by
  apply Finset.disjoint_left.mpr
  intro q h hs
  obtain ⟨⟨i, a⟩, _, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hz, ho, hp, hn, hd⟩ := exclusions i a
  rw [BlowupDoubleLineSingletonBenchmark.twoBlowups, Finset.mem_union] at h
  exact h.elim (BlowupDoubleLineSingletonBenchmark.not_mem_previous_singleton rfl hz ho hp hn) hd

/-- Ten distinct requests beyond the preceding 1,047 certified queries. -/
theorem card_twoBlowups : twoBlowups.card = 1057 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDoubleLineSingletonBenchmark.card_twoBlowups,
    show singletons.card = 10 by decide +kernel]

/-- Every request counted has its original geometric domain and an arithmetic certificate. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  rw [twoBlowups, Finset.mem_union] at h
  rcases h with h | h
  · exact BlowupDoubleLineSingletonBenchmark.twoBlowups_checked h
  · obtain ⟨⟨i, a⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨domain i a, value i a, checked i a⟩

end AxiomaticGW.GKM.BlowupRulingSingletonBenchmark
