/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupFewMarkingCoverage
public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalReplay

/-! # The verified two-point blowup benchmark including the mixed exceptional class -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoMixedExceptional
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupFewMarkingCoverage

private abbrev supported := GenusTwoExceptionalFewMarkings.TwoBlowups.requests

private theorem overlap : twoBlowups ∩ Finset.univ.image requests =
    (higherSupport.filter fun i ↦ (supported i).beta = ![1, 1, 0]).image supported := by
  ext q
  constructor
  · rintro h
    obtain ⟨hold, hnew⟩ := Finset.mem_inter.mp h
    rw [coverage, Finset.mem_filter] at hnew
    rcases Finset.mem_union.mp hold with hlow | hhigh
    · rw [GenusTwoEnergyOne.TwoBlowups.coverage, mem_fewMarkingsAtEnergy_iff] at hlow
      have he := hlow.2
      rw [hnew.2] at he
      exact False.elim ((by decide +kernel :
        SurfaceTarget.blowupTwo.effective.energy ![1, 1, 0] ≠ 1) he)
    · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hhigh
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨hj, (congrArg SurfaceQuery.beta hjq).trans hnew.2⟩, hjq⟩
  · intro h
    obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp h
    obtain ⟨hhigh, hbeta⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_inter.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hhigh, hjq⟩), ?_⟩
    rw [coverage, Finset.mem_filter, mem_fewMarkingQueries_iff, ← hjq]
    exact ⟨(GenusTwoExceptionalFewMarkings.TwoBlowups.accepted j).1, hbeta⟩

/-- The 29 previously supported queries in this class are counted once in the 790-element union. -/
theorem card_with_mixed_exceptional : (twoBlowups ∪ Finset.univ.image requests).card = 790 := by
  have h := Finset.card_union_add_card_inter twoBlowups (Finset.univ.image requests)
  have hover : (twoBlowups ∩ Finset.univ.image requests).card = 29 := by
    rw [overlap]
    decide +kernel
  rw [card_twoBlowups, Finset.card_image_of_injective _ requests_injective,
    Finset.card_univ, Fintype.card_fin, hover] at h
  omega

/-- Every query counted by the union has its own reconstruction witness. -/
theorem checked_of_mem_union {q : SurfaceQuery .blowupTwo}
    (h : q ∈ twoBlowups ∪ Finset.univ.image requests) :
    FewMarkingQuery q ∧ ∃ a, CheckedDescendant 0 q a := by
  rcases Finset.mem_union.mp h with hold | hnew
  · exact twoBlowups_checked hold
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hnew
    exact ⟨(frame i).1, values i, accepted i⟩

end AxiomaticGW.GKM.BlowupTwoMixedExceptional
