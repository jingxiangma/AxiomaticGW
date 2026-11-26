/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalCoverage
public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalMarked
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoMixedExceptionalInteriorPairs

/-! # All ordinary genus-two descendants with up to two markings in class E₁+E₂ -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoMixedExceptional
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoMixedExceptionalInteriorPairs (index)

private theorem partition_rows : ∀ j : Fin 100, j ∈ reducedIndices ∨ ∃ k, index k = j := by
  decide +kernel

private theorem interior_binding : ∀ k : Fin 32,
    (requests (Fin.natAdd 5 (index k)), values (Fin.natAdd 5 (index k))) =
      (BlowupTwoMixedExceptionalInteriorPairs.requests k,
       BlowupTwoMixedExceptionalInteriorPairs.values k) := by decide +kernel

/-- All 105 ordered native queries agree with an original reconstruction or support proof. -/
theorem accepted (i : Fin 105) : CheckedDescendant 0 (requests i) (values i) := by
  refine Fin.addCases (m := 5) (n := 100) (fun j ↦ .mixed (singleton_accepted j)) ?_ i
  intro j
  rcases partition_rows j with hj | ⟨k, rfl⟩
  · exact reduced_accepted hj
  · exact (congrArg (fun r ↦ CheckedDescendant 0 r.1 r.2) (interior_binding k)).mpr
      (.mixed (BlowupTwoMixedExceptionalInteriorPairs.accepted k))

set_option maxRecDepth 4096 in
/-- Every dimension-compatible few-marking input in E₁+E₂ has a unique certified zero row. -/
theorem unique_comparison {q : SurfaceQuery .blowupTwo} (hq : FewMarkingQuery q)
    (hb : q.beta = ![1, 1, 0]) : ∃! i, requests i = q ∧ CheckedDescendant 0 q 0 ∧
      values i = 0 ∧ equivariant i = 0 ∧ EquivariantCoefficients.Specializes (equivariant i) 0 := by
  have hm : q ∈ (fewMarkingQueries .blowupTwo).filter (fun r ↦ r.beta = ![1, 1, 0]) :=
    Finset.mem_filter.mpr ⟨(mem_fewMarkingQueries_iff q).mpr hq, hb⟩
  rw [← coverage] at hm
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
  have hz : values i = 0 := (by decide +kernel : ∀ j, values j = 0) i
  refine ⟨i, ⟨rfl, hz ▸ accepted i, hz, ?_, hz ▸ specializes i⟩, ?_⟩
  · rw [equivariant_eq_ordinary, hz, Rat.cast_zero]
  · exact fun j hj ↦ requests_injective hj.1

end AxiomaticGW.GKM.BlowupTwoMixedExceptional
