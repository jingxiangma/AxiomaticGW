/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalBenchmark
public import AxiomaticGW.Surfaces.GenusTwoZeroDivisorBenchmark

/-! # Distinct checked blowup requests after the zero-coefficient divisor reduction

The additional requests exclude the previous energy slices, exceptional point support,
and the two-point blowup's full mixed exceptional class. All counts are cardinalities
of sets of full ordered queries.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDivisorBenchmarkCoverage
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open ZeroDivisorBenchmark (additionalSuite outsideFixedSlices mem_additionalSuite)

/-- The F₁ certified suite after adjoining all additional divisor zeros. -/
def oneBlowup : Finset (SurfaceQuery .hirzebruchOne) :=
  BlowupFewMarkingCoverage.oneBlowup ∪ additionalSuite .hirzebruchOne

/-- The two-point blowup certified suite, including the entire class E₁+E₂. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  (BlowupFewMarkingCoverage.twoBlowups ∪ Finset.univ.image BlowupTwoMixedExceptional.requests) ∪
    additionalSuite .blowupTwo

private theorem separate {X : SurfaceTarget} (s : Finset (SurfaceQuery X))
    (excluded : ∀ q ∈ s, outsideFixedSlices X q = false) : Disjoint s (additionalSuite X) := by
  apply Finset.disjoint_left.mpr
  intro q h₁ h₂
  have h := ((mem_additionalSuite q).mp h₂).2.1
  rw [excluded q h₁] at h
  cases h

/-- Energy one, energy two and the exceptional point-support frame on F₁ are all excluded. -/
theorem oneBlowup_disjoint :
    Disjoint BlowupFewMarkingCoverage.oneBlowup (additionalSuite .hirzebruchOne) := by
  apply separate
  intro q h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rw [GenusTwoEnergyOne.OneBlowup.coverage, mem_fewMarkingsAtEnergy_iff] at h
      simp [outsideFixedSlices, h.2]
    · rw [F1EnergyTwo.coverage, mem_fewMarkingsAtEnergy_iff] at h
      simp [outsideFixedSlices, h.2]
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    simp [outsideFixedSlices, (GenusTwoExceptionalFewMarkings.OneBlowup.accepted i).2]

/-- The new two-point blowup rows exclude energy one, prior point support and E₁+E₂. -/
theorem twoBlowups_disjoint :
    Disjoint (BlowupFewMarkingCoverage.twoBlowups ∪
      Finset.univ.image BlowupTwoMixedExceptional.requests) (additionalSuite .blowupTwo) := by
  apply separate
  intro q h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rw [GenusTwoEnergyOne.TwoBlowups.coverage, mem_fewMarkingsAtEnergy_iff] at h
      simp [outsideFixedSlices, h.2]
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      simp [outsideFixedSlices, (GenusTwoExceptionalFewMarkings.TwoBlowups.accepted i).2]
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    simp [outsideFixedSlices, (BlowupTwoMixedExceptional.frame i).2]

/-- The two unions contain exactly 263 and 906 distinct original ordered requests. -/
theorem benchmark_sizes : oneBlowup.card = 263 ∧ twoBlowups.card = 906 := by
  constructor
  · rw [oneBlowup, Finset.card_union_of_disjoint oneBlowup_disjoint,
      BlowupFewMarkingCoverage.card_oneBlowup, ZeroDivisorBenchmark.card_additionalSuite.1]
  · rw [twoBlowups, Finset.card_union_of_disjoint twoBlowups_disjoint,
      BlowupTwoMixedExceptional.card_with_mixed_exceptional,
      ZeroDivisorBenchmark.card_additionalSuite.2]

private theorem additional_checked {X : SurfaceTarget} (i : Fin X.blowups) {q : SurfaceQuery X}
    (h : q ∈ additionalSuite X) : FewMarkingQuery q ∧ ∃ v, CheckedDescendant i q v := by
  obtain ⟨hq, _, hz⟩ := (mem_additionalSuite q).mp h
  exact ⟨hq, 0, zeroDivisorPair?_checked i q hz⟩

/-- Every one of the 263 F₁ requests is in the benchmark and has a checked numerical witness. -/
theorem oneBlowup_checked {q : SurfaceQuery .hirzebruchOne} (h : q ∈ oneBlowup) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  exact (Finset.mem_union.mp h).elim BlowupFewMarkingCoverage.oneBlowup_checked
    (additional_checked 0)

/-- Every one of the 906 two-point blowup requests has its own ordered arithmetic witness. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  exact (Finset.mem_union.mp h).elim BlowupTwoMixedExceptional.checked_of_mem_union
    (additional_checked 0)

end AxiomaticGW.GKM.BlowupDivisorBenchmarkCoverage
