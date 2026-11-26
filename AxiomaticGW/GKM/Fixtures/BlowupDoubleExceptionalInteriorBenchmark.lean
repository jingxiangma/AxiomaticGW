/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupDoubleExceptionalMarkedBenchmark
public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalComparison
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs

/-! # Complete two-marking benchmarks on the doubled exceptional curves of Bl₂

The 64 interior requests are disjoint from the previous 978 checked requests.
The complete 105-row slice on each axis is specified independently by the virtual dimension.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupDoubleExceptionalInteriorBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupTwoDoubleExceptionalInteriorPairs
open BlowupTwoDoubleExceptionalDivisor (beta)

set_option maxRecDepth 65536

/-- The 32 genuine interior requests on a specified full class. -/
def atAxis (i : Fin 2) : Finset (SurfaceQuery X) := Finset.univ.image (requests i)

/-- Both full axes and both original marking orders. -/
def rows : Finset (SurfaceQuery X) := Finset.univ.biUnion atAxis

/-- The cumulative checked query set for the two-point blowup. -/
def twoBlowups : Finset (SurfaceQuery X) := BlowupDoubleExceptionalMarkedBenchmark.twoBlowups ∪ rows

private theorem mem_rows {q : SurfaceQuery X} (h : q ∈ rows) : ∃ i j, q = requests i j := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨i, j, rfl⟩

private theorem outside (i : Fin 2) (j : Fin 32) : let q := requests i j
    (X.effective.energy q.beta ≠ 1 ∧ exceptionalPointQueryValue? q ≠ some 0 ∧
      q.beta ≠ ![1,1,0] ∧ zeroDivisorPair? q ≠ some 0) ∧
    q ∉ BlowupDoubleExceptionalPairBenchmark.pairs ∧
    BlowupTwoDoubleExceptionalMarked.recognized q = false := by
  revert i j
  decide +kernel

-- The finite-suite decompositions are used only by their stated union identities.
attribute [local irreducible] fewMarkingQueries twoBlowups
  BlowupDoubleExceptionalMarkedBenchmark.twoBlowups
  BlowupDoubleExceptionalSingletonBenchmark.twoBlowups
  BlowupDoubleExceptionalPairBenchmark.twoBlowups
  BlowupDoubleExceptionalBenchmark.twoBlowups BlowupDivisorBenchmarkCoverage.twoBlowups
  BlowupFewMarkingCoverage.twoBlowups

/-- No interior request can already be counted as a marked reduction, singleton, point-supported
vanishing, primitive-class reconstruction or mixed exceptional query. -/
theorem disjoint : Disjoint BlowupDoubleExceptionalMarkedBenchmark.twoBlowups rows := by
  apply Finset.disjoint_left.mpr
  intro q he hi
  obtain ⟨i, j, rfl⟩ := mem_rows hi
  obtain ⟨h₁, hp, hm⟩ := outside i j
  rw [BlowupDoubleExceptionalMarkedBenchmark.twoBlowups, Finset.mem_union] at he
  rcases he with h | h
  · rw [BlowupDoubleExceptionalSingletonBenchmark.twoBlowups, Finset.mem_union] at h
    rcases h with h | h
    · rw [BlowupDoubleExceptionalPairBenchmark.twoBlowups, Finset.mem_union] at h
      rcases h with h | h
      · rw [BlowupDoubleExceptionalBenchmark.twoBlowups, Finset.mem_union] at h
        rcases h with h | h
        · exact BlowupDoubleExceptionalBenchmark.not_mem_previous h₁ h
        · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
          exact (by decide : (1 : ℕ) ≠ 2) (congrArg (fun q ↦ q.insertions.length) ha)
      · exact hp h
    · obtain ⟨⟨a, r⟩, _, ha⟩ := Finset.mem_image.mp h
      exact (by decide : (1 : ℕ) ≠ 2) (congrArg (fun q ↦ q.insertions.length) ha)
  · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp h).1
    have ht := ((BlowupTwoDoubleExceptionalMarked.mem_atAxis_iff a _).mp ha).2.2.2.2
    exact Bool.noConfusion (hm.symm.trans ht)

/-- The 64 additional requests give 1,042 distinct checked queries on Bl₂. -/
theorem card_twoBlowups : twoBlowups.card = 1042 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupDoubleExceptionalMarkedBenchmark.card_twoBlowups, show rows.card = 64 by decide +kernel]

/-- Each counted request has a full-class reconstruction witness and the required dimension. -/
theorem twoBlowups_checked {q : SurfaceQuery X} (h : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  rw [twoBlowups, Finset.mem_union] at h
  rcases h with h | h
  · exact BlowupDoubleExceptionalMarkedBenchmark.twoBlowups_checked h
  · obtain ⟨i, j, rfl⟩ := mem_rows h
    exact ⟨domain i j, values i j, checked i j⟩

/-- The full dimension-compatible one- and two-marked slice on the indicated doubled axis. -/
def axisSuite (i : Fin 2) : Finset (SurfaceQuery X) :=
  (dimensionShapes X 2).image (fun m ↦ ⟨2, beta i, m⟩)

/-- The 29 archived point-supported indices on the selected doubled class, in archival order. -/
def pointIndex (i : Fin 2) (j : Fin 29) : Fin 514 :=
  ⟨(if i = 0 then 268 else 20) + j.val, by split <;> omega⟩

private def points (i : Fin 2) : Finset (SurfaceQuery X) :=
  Finset.univ.image (fun j ↦ GenusTwoExceptionalFewMarkings.TwoBlowups.requests (pointIndex i j))

private theorem points_mem (i : Fin 2) {q : SurfaceQuery X} (h : q ∈ points i) :
    q ∈ twoBlowups := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
  rw [twoBlowups]
  apply Finset.mem_union_left
  rw [BlowupDoubleExceptionalMarkedBenchmark.twoBlowups]
  apply Finset.mem_union_left
  rw [BlowupDoubleExceptionalSingletonBenchmark.twoBlowups]
  apply Finset.mem_union_left
  rw [BlowupDoubleExceptionalPairBenchmark.twoBlowups]
  apply Finset.mem_union_left
  rw [BlowupDoubleExceptionalBenchmark.twoBlowups]
  apply Finset.mem_union_left
  rw [BlowupDivisorBenchmarkCoverage.twoBlowups]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [BlowupFewMarkingCoverage.twoBlowups]
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨pointIndex i j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  revert i j
  decide +kernel

private theorem classification (j : Fin 210) :
    let q := BlowupTwoDoubleExceptionalFewMarkings.requests j
    ∃ i, q.beta = beta i ∧ ((∃ a, q = BlowupTwoDoubleExceptionalSingletons.request i a) ∨
      (q.insertions.length = 2 ∧ BlowupTwoDoubleExceptionalMarked.recognized q = true) ∨
      (∃ r, q = GenusTwoExceptionalFewMarkings.TwoBlowups.requests (pointIndex i r)) ∨
      ∃ r, q = requests i r) := by
  revert j
  decide +kernel

private theorem classified_mem (j : Fin 210) (hd : FewMarkingQuery
    (BlowupTwoDoubleExceptionalFewMarkings.requests j)) :
    BlowupTwoDoubleExceptionalFewMarkings.requests j ∈ twoBlowups := by
  obtain ⟨i, hb, h | h | h | h⟩ := classification j
  · obtain ⟨a, ha⟩ := h
    rw [ha, twoBlowups]
    apply Finset.mem_union_left
    rw [BlowupDoubleExceptionalMarkedBenchmark.twoBlowups]
    exact Finset.mem_union_left _ (BlowupDoubleExceptionalSingletonBenchmark.mem_twoBlowups i a)
  · rw [twoBlowups]
    apply Finset.mem_union_left
    apply BlowupDoubleExceptionalMarkedBenchmark.rows_subset
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, (BlowupTwoDoubleExceptionalMarked.mem_atAxis_iff i _).mpr
      ⟨hd.1, hb, h.1, hd.2.2.2.2, h.2⟩⟩
  · obtain ⟨r, hr⟩ := h
    exact points_mem i (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr.symm⟩)
  · obtain ⟨r, hr⟩ := h
    rw [hr, twoBlowups]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩)

/-- Each axis has every one of the independently enumerated 105 ordered dimension-compatible
queries in the cumulative checked suite. Only the request frame of the native archive is used. -/
theorem axis_coverage (i : Fin 2) : (axisSuite i).card = 105 ∧ axisSuite i ⊆ twoBlowups := by
  have he : X.effective.energy (beta i) = 2 := by fin_cases i <;> decide +kernel
  constructor
  · rw [axisSuite, Finset.card_image_of_injective _
      (fun m n h ↦ congrArg SurfaceQuery.insertions h), card_dimensionShapes]
    decide +kernel
  · intro q hq
    have hf := fewMarkingQueries_filter_class (beta i)
      (by change 0 < X.effective.energy (beta i); rw [he]; decide)
      (by change X.effective.energy (beta i) ≤ 4; rw [he]; decide)
    rw [he] at hf
    change (fewMarkingQueries X).filter _ = axisSuite i at hf
    have hmclass : q ∈ (fewMarkingQueries X).filter (fun q ↦ q.beta = beta i) := by rwa [hf]
    obtain ⟨hd, hb⟩ := Finset.mem_filter.mp hmclass
    have hm : q ∈ Finset.univ.image BlowupTwoDoubleExceptionalFewMarkings.requests := by
      rw [BlowupTwoDoubleExceptionalFewMarkings.complete, Finset.mem_union]
      have hc : beta i = ![2,0,0] ∨ beta i = ![0,2,0] := by fin_cases i <;> decide +kernel
      exact hc.elim (fun e ↦ Or.inl (Finset.mem_filter.mpr ⟨hd, hb.trans e⟩))
        (fun e ↦ Or.inr (Finset.mem_filter.mpr ⟨hd, hb.trans e⟩))
    have dom : FewMarkingQuery q := (mem_fewMarkingQueries_iff (X := X) q).mp hd
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact hj ▸ classified_mem j (hj.symm ▸ dom)

/-- Each one- or two-marked request of the geometric dimension on either doubled axis is covered. -/
theorem checked_at_axis (i : Fin 2) (q : SurfaceQuery X) (hg : q.genus = 2)
    (hb : q.beta = beta i) (hn : q.insertions.length ≤ 2) (hd : q.DimensionCompatible) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  apply twoBlowups_checked
  apply (axis_coverage i).2
  have he : X.effective.energy (beta i) = 2 := by fin_cases i <;> decide +kernel
  have hq : (⟨2, beta i, q.insertions⟩ : SurfaceQuery X) = q :=
    (SurfaceQuery.eq_iff _ _).mpr ⟨hg.symm, hb.symm, rfl⟩
  refine Finset.mem_image.mpr ⟨q.insertions, ?_, hq⟩
  rw [← he, mem_dimensionShapes_iff (beta i) (by rw [he]; decide)]
  exact ⟨hn, hq.symm ▸ hd⟩

end AxiomaticGW.GKM.BlowupDoubleExceptionalInteriorBenchmark
