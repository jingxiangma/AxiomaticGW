/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalInteriorBenchmark
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineOneMarking

/-! # Five new basis singleton queries at twice the strict line -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDoubleLineSingletonBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleLine

/-- The unit, three divisors and point at the complete doubled strict-line class. -/
def singletons : Finset (SurfaceQuery .blowupTwo) := Finset.univ.image request

/-- Cumulative verified few-marking requests on the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  BlowupDoubleExceptionalInteriorBenchmark.twoBlowups ∪ singletons

private theorem exclusions (a : SurfaceBasisLabel .blowupTwo) : let q := request a
    (SurfaceTarget.blowupTwo.effective.energy q.beta ≠ 1 ∧
      exceptionalPointQueryValue? q ≠ some 0 ∧ q.beta ≠ ![1, 1, 0] ∧ zeroDivisorPair? q ≠ some 0) ∧
    q ∉ Finset.univ.image BlowupTwoDoubleExceptionalDivisor.request ∧
    q ∉ BlowupDoubleExceptionalPairBenchmark.pairs ∧
    q ∉ BlowupDoubleExceptionalSingletonBenchmark.additional := by
  revert a
  decide +kernel

-- These cumulative suites enter only through their proved finite union descriptions.
attribute [local irreducible] twoBlowups BlowupDoubleExceptionalInteriorBenchmark.twoBlowups
  BlowupDoubleExceptionalMarkedBenchmark.twoBlowups
  BlowupDoubleExceptionalSingletonBenchmark.twoBlowups
  BlowupDoubleExceptionalPairBenchmark.twoBlowups BlowupDoubleExceptionalBenchmark.twoBlowups

/-- Exclude a singleton from the entire earlier suite using the primitive, incidence,
mixed-exceptional and doubled-exceptional tests. -/
theorem not_mem_previous_singleton {q : SurfaceQuery .blowupTwo} (hl : q.insertions.length = 1)
    (hz : SurfaceTarget.blowupTwo.effective.energy q.beta ≠ 1 ∧
      exceptionalPointQueryValue? q ≠ some 0 ∧ q.beta ≠ ![1, 1, 0] ∧ zeroDivisorPair? q ≠ some 0)
    (ho : q ∉ Finset.univ.image BlowupTwoDoubleExceptionalDivisor.request)
    (hp : q ∉ BlowupDoubleExceptionalPairBenchmark.pairs)
    (hn : q ∉ BlowupDoubleExceptionalSingletonBenchmark.additional) :
    q ∉ BlowupDoubleExceptionalInteriorBenchmark.twoBlowups := by
  intro h
  rw [BlowupDoubleExceptionalInteriorBenchmark.twoBlowups, Finset.mem_union] at h
  rcases h with h | h
  · rw [BlowupDoubleExceptionalMarkedBenchmark.twoBlowups, Finset.mem_union] at h
    rcases h with h | h
    · rw [BlowupDoubleExceptionalSingletonBenchmark.twoBlowups, Finset.mem_union] at h
      rcases h with h | h
      · rw [BlowupDoubleExceptionalPairBenchmark.twoBlowups, Finset.mem_union] at h
        rcases h with h | h
        · rw [BlowupDoubleExceptionalBenchmark.twoBlowups, Finset.mem_union] at h
          exact h.elim (BlowupDoubleExceptionalBenchmark.not_mem_previous hz) ho
        · exact hp h
      · exact hn h
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp h).1
      have hlen := ((BlowupTwoDoubleExceptionalMarked.mem_atAxis_iff i _).mp hi).2.2.1
      exact (by decide : (1 : ℕ) ≠ 2) (hl.symm.trans hlen)
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact (by decide : (2 : ℕ) ≠ 1) ((congrArg (fun q ↦ q.insertions.length) hj).trans hl)

/-- Every new singleton lies outside all previously certified full-class frames. -/
theorem disjoint : Disjoint BlowupDoubleExceptionalInteriorBenchmark.twoBlowups singletons := by
  apply Finset.disjoint_left.mpr
  intro q h hs
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hz, ho, hp, hn⟩ := exclusions a
  exact not_mem_previous_singleton rfl hz ho hp hn h

/-- The full fixed two-point-blowup suite gains five distinct requests at 2L. -/
theorem card_twoBlowups : twoBlowups.card = 1047 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDoubleExceptionalInteriorBenchmark.card_twoBlowups,
    show singletons.card = 5 by decide +kernel]

/-- Every counted query has the required full domain and its arithmetic reconstruction witness. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  rw [twoBlowups, Finset.mem_union] at h
  rcases h with h | h
  · exact BlowupDoubleExceptionalInteriorBenchmark.twoBlowups_checked h
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨domain a, value a, checked a⟩

end AxiomaticGW.GKM.BlowupDoubleLineSingletonBenchmark
