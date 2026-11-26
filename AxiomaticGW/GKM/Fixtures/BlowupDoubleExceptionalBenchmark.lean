/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDivisorBenchmarkCoverage
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalDivisor

/-! # Bounded Bl₂ benchmark with the two double-exceptional divisor singletons -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDoubleExceptionalBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleExceptionalDivisor (request)

/-- Adjoin the two original ordered double-exceptional requests to the verified suite. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  BlowupDivisorBenchmarkCoverage.twoBlowups ∪ Finset.univ.image request

/-- Exclude a full query from the four parts of the 906-row suite by the tests which
define each part: energy, point support, the mixed class, and the zero-coefficient pair. -/
theorem not_mem_previous {q : SurfaceQuery .blowupTwo}
    (outside : SurfaceTarget.blowupTwo.effective.energy q.beta ≠ 1 ∧
      exceptionalPointQueryValue? q ≠ some 0 ∧ q.beta ≠ ![1, 1, 0] ∧
      zeroDivisorPair? q ≠ some 0) : q ∉ BlowupDivisorBenchmarkCoverage.twoBlowups := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · rw [GenusTwoEnergyOne.TwoBlowups.coverage, mem_fewMarkingsAtEnergy_iff] at h
        exact outside.1 h.2
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
        exact outside.2.1 (hj ▸ (GenusTwoExceptionalFewMarkings.TwoBlowups.accepted j).2)
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      exact outside.2.2.1 (hj ▸ (BlowupTwoMixedExceptional.frame j).2)
  · exact outside.2.2.2 ((ZeroDivisorBenchmark.mem_additionalSuite _).mp h).2.2

/-- The double-exceptional divisor singletons are disjoint from the earlier suite. -/
theorem disjoint : Disjoint BlowupDivisorBenchmarkCoverage.twoBlowups
    (Finset.univ.image request) := by
  apply Finset.disjoint_left.mpr
  intro q h hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  apply not_mem_previous _ h
  fin_cases i <;> decide +kernel

/-- There are exactly 908 distinct original ordered Bl₂ queries in the enlarged suite. -/
theorem card_twoBlowups : twoBlowups.card = 908 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDivisorBenchmarkCoverage.benchmark_sizes.2]
  decide +kernel

/-- Every member has an arithmetic witness at its original full class and ordered insertions. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant 0 q a := by
  rcases Finset.mem_union.mp h with h | h
  · exact BlowupDivisorBenchmarkCoverage.twoBlowups_checked h
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨BlowupTwoDoubleExceptionalDivisor.domain i, 3/320,
      BlowupTwoDoubleExceptionalDivisor.checked i⟩

end AxiomaticGW.GKM.BlowupDoubleExceptionalBenchmark
