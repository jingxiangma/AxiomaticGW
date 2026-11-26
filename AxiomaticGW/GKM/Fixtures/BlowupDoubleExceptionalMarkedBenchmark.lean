/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalSingletonBenchmark
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalMarked

/-! # Exact coverage of all marked-equation pairs on twice either exceptional curve -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDoubleExceptionalMarkedBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleExceptionalMarked
open BlowupTwoDoubleExceptionalDivisor (beta)

set_option maxRecDepth 65536

/-- All 100 original ordered rows, split by full curve rather than by energy alone. -/
def rows : Finset (SurfaceQuery .blowupTwo) := Finset.univ.biUnion atAxis

/-- Point support, the vanishing-coefficient divisor rule, and the twelve earlier signed rows
account for all overlaps with the previously certified pairs. -/
def fresh (q : SurfaceQuery .blowupTwo) : Bool :=
  (exceptionalPointQueryValue? q).isNone && (zeroDivisorPair? q).isNone &&
    decide (q ∉ BlowupDoubleExceptionalPairBenchmark.pairs)

/-- New requests selected from the exact current frame. -/
def additional : Finset (SurfaceQuery .blowupTwo) := rows.filter (fun q ↦ fresh q = true)

/-- The cumulative verified few-marking suite on the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery .blowupTwo) :=
  BlowupDoubleExceptionalSingletonBenchmark.twoBlowups ∪ additional

private theorem mem_rows {q : SurfaceQuery .blowupTwo} (h : q ∈ rows) :
    ∃ i r a last, q = request i r a last := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
  obtain ⟨⟨r, a, last⟩, _, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨i, r, a, last, rfl⟩

/-- Per-axis decomposition of the original 50 pairs. The four disjoint counts are
point support, the other zero-divisor rows, previous nonzero pairs, and new pairs. -/
theorem axis_counts (i : Fin 2) : let s := atAxis i
    s.card = 50 ∧ (s.filter (fun q ↦ (exceptionalPointQueryValue? q).isSome)).card = 10 ∧
    (s.filter (fun q ↦ (exceptionalPointQueryValue? q).isNone &&
      (zeroDivisorPair? q).isSome)).card = 8 ∧
    (s.filter (fun q ↦ q ∈ BlowupDoubleExceptionalPairBenchmark.pairs)).card = 6 ∧
    (s.filter (fun q ↦ fresh q = true)).card = 26 := by fin_cases i <;> decide +kernel

/-- The two-axis frame has 100 original requests and adds exactly 52. -/
theorem frame_counts : rows.card = 100 ∧ additional.card = 52 := by decide +kernel

private theorem shape (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool) :
    let q := request i r a last
    q.insertions.length = 2 ∧ SurfaceTarget.blowupTwo.effective.energy q.beta = 2 ∧
      q.beta ≠ ![1, 1, 0] := by
  revert i r a last
  decide +kernel

/-- Point-supported rows in the archived 514-row frame, checked by their complete requests. -/
private def pointIndex (i : Fin 2) (r : Fin 5) (last : Bool) : Fin 514 :=
  let rows : Fin 2 → Fin 5 → Fin 2 → Fin 514 :=
    ![![![269,285], ![270,284], ![273,288], ![276,291], ![279,294]],
      ![![21,37], ![22,36], ![25,40], ![28,43], ![31,46]]]
  rows i r (if last then 1 else 0)

private theorem point_old (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool)
    (h : (exceptionalPointQueryValue? (request i r a last)).isSome = true) :
    request i r a last ∈ BlowupDoubleExceptionalSingletonBenchmark.twoBlowups := by
  rw [BlowupDoubleExceptionalSingletonBenchmark.twoBlowups]
  refine Finset.mem_union_left _ ?_
  rw [BlowupDoubleExceptionalPairBenchmark.twoBlowups]
  refine Finset.mem_union_left _ ?_
  rw [BlowupDoubleExceptionalBenchmark.twoBlowups]
  refine Finset.mem_union_left _ ?_
  rw [BlowupDivisorBenchmarkCoverage.twoBlowups]
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  rw [BlowupFewMarkingCoverage.twoBlowups]
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  let j := pointIndex i r last
  have he : ∀ (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool),
      (exceptionalPointQueryValue? (request i r a last)).isSome = true →
      GenusTwoExceptionalFewMarkings.TwoBlowups.requests (pointIndex i r last) =
        request i r a last := by decide +kernel
  have hj := he i r a last h
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
  change 1 < SurfaceTarget.blowupTwo.effective.energy
    (GenusTwoExceptionalFewMarkings.TwoBlowups.requests (pointIndex i r last)).beta
  rw [hj, (shape i r a last).2.1]
  decide

private theorem zero_old (i : Fin 2) (r : Fin 5) (a : SurfaceBasisLabel .blowupTwo) (last : Bool)
    (hp : (exceptionalPointQueryValue? (request i r a last)).isNone = true)
    (hz : (zeroDivisorPair? (request i r a last)).isSome = true) :
    request i r a last ∈ BlowupDoubleExceptionalSingletonBenchmark.twoBlowups := by
  rw [BlowupDoubleExceptionalSingletonBenchmark.twoBlowups]
  refine Finset.mem_union_left _ ?_
  rw [BlowupDoubleExceptionalPairBenchmark.twoBlowups]
  refine Finset.mem_union_left _ ?_
  rw [BlowupDoubleExceptionalBenchmark.twoBlowups]
  refine Finset.mem_union_left _ ?_
  rw [BlowupDivisorBenchmarkCoverage.twoBlowups]
  apply Finset.mem_union_right
  apply (ZeroDivisorBenchmark.mem_additionalSuite _).mpr
  obtain ⟨_, he, hm⟩ := shape i r a last
  refine ⟨domain i r a last, ?_, ?_⟩
  · simp [ZeroDivisorBenchmark.outsideFixedSlices, hp, he, hm]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hz
    have hzero := (zeroDivisorPair?_iff _ _).mp hv
    exact hv.trans (congrArg some hzero.1)

/-- The 52 additional queries lie outside the previous 926-row suite. -/
theorem disjoint : Disjoint BlowupDoubleExceptionalSingletonBenchmark.twoBlowups additional := by
  apply Finset.disjoint_left.mpr
  intro q h hn
  obtain ⟨hr, hf⟩ := Finset.mem_filter.mp hn
  obtain ⟨i, r, a, last, rfl⟩ := mem_rows hr
  simp only [fresh, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨hp, hz⟩, hn⟩ := hf
  obtain ⟨har, he, hm⟩ := shape i r a last
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · apply BlowupDoubleExceptionalBenchmark.not_mem_previous _ h
        exact ⟨by omega, by simp [Option.isNone_iff_eq_none.mp hp], hm,
          by simp [Option.isNone_iff_eq_none.mp hz]⟩
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
        exact (by decide : (1 : ℕ) ≠ 2) ((congrArg (fun q ↦ q.insertions.length) hj).trans har)
    · exact hn h
  · obtain ⟨⟨j, t⟩, _, hj⟩ := Finset.mem_image.mp h
    exact (by decide : (1 : ℕ) ≠ 2) ((congrArg (fun q ↦ q.insertions.length) hj).trans har)

private theorem earlier_pair {q : SurfaceQuery .blowupTwo}
    (h : q ∈ BlowupDoubleExceptionalPairBenchmark.pairs) :
    q ∈ BlowupDoubleExceptionalSingletonBenchmark.twoBlowups :=
  Finset.mem_union_left _ (Finset.mem_union_right _ h)

private theorem isNone_of_not_isSome {α : Type} {o : Option α} (h : o.isSome ≠ true) :
    o.isNone = true := by cases o <;> simp_all

-- The remaining proof only uses the established inclusion maps for the prior suite.
attribute [local irreducible] BlowupDoubleExceptionalSingletonBenchmark.twoBlowups

/-- Every one of the 100 marked-equation requests lies in the cumulative suite. -/
theorem rows_subset : rows ⊆ twoBlowups := by
  intro q h
  rw [twoBlowups, Finset.mem_union]
  by_cases hf : fresh q = true
  · exact Or.inr (Finset.mem_filter.mpr ⟨h, hf⟩)
  · apply Or.inl
    obtain ⟨i, r, a, last, rfl⟩ := mem_rows h
    by_cases hp : (exceptionalPointQueryValue? (request i r a last)).isSome = true
    · exact point_old i r a last hp
    · have hp' := isNone_of_not_isSome hp
      by_cases hz : (zeroDivisorPair? (request i r a last)).isSome = true
      · exact zero_old i r a last hp' hz
      · have hz' := isNone_of_not_isSome hz
        have hm : request i r a last ∈ BlowupDoubleExceptionalPairBenchmark.pairs := by
          by_contra wh
          exact hf (by simp only [fresh, hp', hz', Bool.true_and, decide_eq_true wh])
        -- A previously proved one of the twelve nonzero pairs.
        exact earlier_pair hm

/-- Exact distinct cumulative count on the two-point blowup. -/
theorem card_twoBlowups : twoBlowups.card = 978 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDoubleExceptionalSingletonBenchmark.card_twoBlowups, frame_counts.2]

/-- The old suite already contained exactly 48 of the 100 ordered marked-equation pairs. -/
theorem overlap : (BlowupDoubleExceptionalSingletonBenchmark.twoBlowups ∩ rows).card = 48 := by
  have hu : BlowupDoubleExceptionalSingletonBenchmark.twoBlowups ∪ rows = twoBlowups := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset Finset.subset_union_left rows_subset
    · exact Finset.union_subset Finset.subset_union_left (fun _ h ↦
        Finset.mem_union_right _ (Finset.mem_filter.mp h).1)
  have hc := Finset.card_union_add_card_inter
    BlowupDoubleExceptionalSingletonBenchmark.twoBlowups rows
  rw [hu, card_twoBlowups, BlowupDoubleExceptionalSingletonBenchmark.card_twoBlowups,
    frame_counts.1] at hc
  omega

/-- Every counted request belongs to the fixed benchmark and carries its arithmetic witness. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  rcases Finset.mem_union.mp h with h | h
  · exact BlowupDoubleExceptionalSingletonBenchmark.twoBlowups_checked h
  · obtain ⟨i, r, a, last, rfl⟩ := mem_rows (Finset.mem_filter.mp h).1
    exact ⟨domain i r a last, values i r a, checked i r a last⟩

end AxiomaticGW.GKM.BlowupDoubleExceptionalMarkedBenchmark
