/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalTargetReplay
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs

/-! # Target-side reconstruction of all genus-two few-marking requests on 2E₁ and 2E₂ -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleExceptionalFewMarkings
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

private theorem partition : ∀ j : Fin 210, (targetValue? (requests j)).isSome = true ∨
    ∃ (i : Fin 2) (k : Fin 32), (requests j, values j) =
      (BlowupTwoDoubleExceptionalInteriorPairs.requests i k,
       BlowupTwoDoubleExceptionalInteriorPairs.values i k) := by decide +kernel

/-- Every native row agrees with the original two-point-blowup reconstruction, including
the interior cases with positive cotangent powers on both marked points. -/
theorem accepted (j : Fin 210) : CheckedDescendant 0 (requests j) (values j) := by
  rcases partition j with h | ⟨i, k, h⟩
  · exact (target_certified (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)).1
  · exact (congrArg (fun p ↦ CheckedDescendant 0 p.1 p.2) h).mpr
      (BlowupTwoDoubleExceptionalInteriorPairs.checked i k)

/-- Original reconstruction, equality in the exact incoming field and ordinary specialization. -/
theorem certified (j : Fin 210) : CheckedDescendant 0 (requests j) (values j) ∧
    equivariant j = (values j : EquivariantCoefficients.Coefficient) ∧
    EquivariantCoefficients.Specializes (equivariant j) (values j) :=
  ⟨accepted j, equivariant_eq_ordinary j, specializes j⟩

/-- A complete ordered benchmark request on either doubled axis selects a unique certified row. -/
theorem certified_query (q : SurfaceQuery .blowupTwo) (hq : FewMarkingQuery q)
    (hc : q.beta = ![2, 0, 0] ∨ q.beta = ![0, 2, 0]) :
    ∃! j, requests j = q ∧ CheckedDescendant 0 q (values j) ∧
      equivariant j = (values j : EquivariantCoefficients.Coefficient) ∧
      EquivariantCoefficients.Specializes (equivariant j) (values j) := by
  have hm : q ∈ Finset.univ.image requests := by
    rw [complete, Finset.mem_union]
    simp only [Finset.mem_filter, mem_fewMarkingQueries_iff, hq, true_and]
    exact hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
  refine ⟨j, ⟨rfl, certified j⟩, ?_⟩
  rintro k ⟨h, _⟩
  apply Fin.ext
  exact (rowNumber_requests k).symm.trans ((congrArg rowNumber h).trans (rowNumber_requests j))

end AxiomaticGW.GKM.BlowupTwoDoubleExceptionalFewMarkings
