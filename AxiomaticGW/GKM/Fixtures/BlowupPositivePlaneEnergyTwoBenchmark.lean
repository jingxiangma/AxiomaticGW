/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupRulingSingletonBenchmark
public import AxiomaticGW.GKM.Fixtures.BlowupTwoEnergyTwoNativeCoverage
public import AxiomaticGW.GKM.Fixtures.BlowupTwoRulingDivisorPointReplay

/-! # Distinct checked genus-two requests on the three positive-plane curves of energy two -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupPositivePlaneEnergyTwoBenchmark
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants ZeroDivisorBenchmark
open BlowupTwoPositivePlaneEnergyTwoPairs (requests values verifiedRows verified_accepted
  rulingDivisorPoints ruling_divisor_point_accepted)

private abbrev X := SurfaceTarget.blowupTwo

/-- Native indices with reconstruction witnesses in the marked, strict-line point and ruling
divisor–point frames. -/
def pairs := verifiedRows ∪ rulingDivisorPoints

/-- Verified pairs outside the earlier direct zero-divisor results. -/
def additional : Finset (SurfaceQuery .blowupTwo) :=
  (pairs.filter (fun j ↦ zeroDivisorPair? (requests j) ≠ some 0)).image requests

/-- The union with all earlier proved requests on the two-point blowup. -/
def twoBlowups := BlowupRulingSingletonBenchmark.twoBlowups ∪ additional

private def supplements : Finset (SurfaceQuery X) :=
  Finset.univ.image BlowupTwoDoubleExceptionalDivisor.request ∪
    BlowupDoubleExceptionalPairBenchmark.pairs ∪
    BlowupDoubleExceptionalSingletonBenchmark.additional ∪
    BlowupDoubleExceptionalMarkedBenchmark.additional ∪
    BlowupDoubleExceptionalInteriorBenchmark.rows ∪
    BlowupDoubleLineSingletonBenchmark.singletons ∪ BlowupRulingSingletonBenchmark.singletons

-- Use the individual small frames to exclude earlier requests without evaluating the 4,495-row set.
attribute [local irreducible] twoBlowups additionalSuite fewMarkingQueries
  BlowupFewMarkingCoverage.twoBlowups BlowupRulingSingletonBenchmark.twoBlowups
  BlowupDoubleLineSingletonBenchmark.twoBlowups BlowupDoubleExceptionalInteriorBenchmark.twoBlowups
  BlowupDoubleExceptionalMarkedBenchmark.twoBlowups
  BlowupDoubleExceptionalSingletonBenchmark.twoBlowups
  BlowupDoubleExceptionalPairBenchmark.twoBlowups BlowupDoubleExceptionalBenchmark.twoBlowups
  BlowupDivisorBenchmarkCoverage.twoBlowups

private theorem previous : BlowupRulingSingletonBenchmark.twoBlowups =
    BlowupDivisorBenchmarkCoverage.twoBlowups ∪ supplements := by
  simp only [BlowupRulingSingletonBenchmark.twoBlowups,
    BlowupDoubleLineSingletonBenchmark.twoBlowups,
    BlowupDoubleExceptionalInteriorBenchmark.twoBlowups,
    BlowupDoubleExceptionalMarkedBenchmark.twoBlowups,
    BlowupDoubleExceptionalSingletonBenchmark.twoBlowups,
    BlowupDoubleExceptionalPairBenchmark.twoBlowups,
    BlowupDoubleExceptionalBenchmark.twoBlowups, supplements, Finset.union_assoc]

private theorem shape_of_supplement {q : SurfaceQuery X} (hq : q ∈ supplements) :
    q.beta 2 = 0 ∨ q.insertions.length = 1 := by
  simp only [supplements, Finset.union_assoc] at hq
  simp only [Finset.mem_union] at hq
  rcases hq with h | h | h | h | h | h | h
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact Or.inl ((by decide +kernel : ∀ i,
      (BlowupTwoDoubleExceptionalDivisor.request i).beta 2 = 0) i)
  · obtain ⟨⟨i,j,b⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact Or.inl ((by decide +kernel : ∀ i j b,
      (BlowupTwoDoubleExceptionalPairs.request i j b).beta 2 = 0) i j b)
  · obtain ⟨⟨i,j⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr rfl
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp h).1
    obtain ⟨⟨r,a,b⟩, _, rfl⟩ := Finset.mem_image.mp hi
    exact Or.inl ((by decide +kernel : ∀ i r a b,
      (BlowupTwoDoubleExceptionalMarked.request i r a b).beta 2 = 0) i r a b)
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Or.inl ((by decide +kernel : ∀ i j,
      (BlowupTwoDoubleExceptionalInteriorPairs.requests i j).beta 2 = 0) i j)
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr rfl
  · obtain ⟨⟨i,a⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact Or.inr rfl

private theorem frame (j : Fin 300) : let q := requests j
    FewMarkingQuery q ∧ q.insertions.length = 2 ∧ 0 < q.beta 2 ∧
    X.effective.energy q.beta ≠ 1 ∧ exceptionalPointQueryValue? q ≠ some 0 ∧ q.beta ≠ ![1,1,0] ∧
    outsideFixedSlices X q = true := by
  have hd : requests j ∈ fewMarkingsAtEnergy .blowupTwo 2 := by
    rw [← BlowupTwoEnergyTwoNativeCoverage.complete]
    exact Finset.mem_image.mpr ⟨.inr (.inr (.inr j)), Finset.mem_univ _, rfl⟩
  have hg := (mem_fewMarkingsAtEnergy_iff _ _).mp hd
  obtain ⟨hlen, hpos, hpt, hbeta, hout⟩ := (by decide +kernel : ∀ i : Fin 300,
    let q := requests i
    q.insertions.length = 2 ∧ 0 < q.beta 2 ∧ exceptionalPointQueryValue? q = none ∧
      q.beta ≠ ![1,1,0] ∧ outsideFixedSlices X q = true) j
  have he : X.effective.energy (requests j).beta = 2 := hg.2
  exact ⟨hg.1, hlen, hpos, by omega, by rw [hpt]; decide, hbeta, hout⟩

/-- The 178 additional requests are disjoint from the preceding 1,057 cases. -/
theorem disjoint : Disjoint BlowupRulingSingletonBenchmark.twoBlowups additional := by
  apply Finset.disjoint_left.mpr
  intro q hold hnew
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hnew
  obtain ⟨_, hl, hp, he, hpt, hm, _⟩ := frame j
  rw [previous, Finset.mem_union] at hold
  rcases hold with hb | hs
  · exact BlowupDoubleExceptionalBenchmark.not_mem_previous
      ⟨he, hpt, hm, (Finset.mem_filter.mp hj).2⟩ hb
  · rcases shape_of_supplement hs with hb | hl'
    · omega
    · omega

/-- Of the 190 pairs, twelve already have a zero-divisor proof and 178 enter the suite here. -/
theorem counts : pairs.card = 190 ∧ additional.card = 178 := by
  have hinj : Function.Injective requests := by
    intro i j h
    have eqRows : (Sum.inr (Sum.inr (Sum.inr i)) : BlowupTwoEnergyTwoNativeCoverage.Row) =
        .inr (.inr (.inr j)) := BlowupTwoEnergyTwoNativeCoverage.requests_injective h
    exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj eqRows))
  refine ⟨BlowupTwoPositivePlaneEnergyTwoPairs.ruling_divisor_point_counts.2.2, ?_⟩
  rw [additional, Finset.card_image_of_injective _ hinj]
  decide +kernel

/-- Distinct witness count on the two-point blowup after the positive-plane pair proofs. -/
theorem card_twoBlowups : twoBlowups.card = 1235 := by
  rw [twoBlowups, Finset.card_union_of_disjoint disjoint,
    BlowupRulingSingletonBenchmark.card_twoBlowups, counts.2]

/-- Every verified row is in the union, including each of the twelve overlaps. -/
theorem verified_mem {j : Fin 300} (hj : j ∈ pairs) : requests j ∈ twoBlowups := by
  rw [twoBlowups, Finset.mem_union]
  by_cases hz : zeroDivisorPair? (requests j) = some 0
  · left
    rw [previous, Finset.mem_union]
    left
    have hbase : requests j ∈ additionalSuite X := (mem_additionalSuite (requests j)).mpr
      ⟨(frame j).1, (frame j).2.2.2.2.2.2, hz⟩
    rw [BlowupDivisorBenchmarkCoverage.twoBlowups]
    exact Finset.mem_union_right _ hbase
  · exact Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hz⟩, rfl⟩)

/-- The count includes only true benchmark queries with an original reconstruction witness. -/
theorem twoBlowups_checked {q : SurfaceQuery .blowupTwo} (hq : q ∈ twoBlowups) :
    FewMarkingQuery q ∧ ∃ v, CheckedDescendant 0 q v := by
  rw [twoBlowups, Finset.mem_union] at hq
  rcases hq with h | h
  · exact BlowupRulingSingletonBenchmark.twoBlowups_checked h
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    refine ⟨(frame j).1, values j, ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hj).1 with hp | hr
    · exact verified_accepted hp
    · exact ruling_divisor_point_accepted hr

end AxiomaticGW.GKM.BlowupPositivePlaneEnergyTwoBenchmark
