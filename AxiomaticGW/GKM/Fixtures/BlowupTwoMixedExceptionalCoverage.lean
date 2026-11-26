/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptional
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingCounts

/-! # Completeness of the genus-two few-marking frame in class E₁+E₂ -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoMixedExceptional
open SurfaceGenusTwo

/-- The original genus, dimension condition, and full curve class hold in every row. -/
theorem frame : ∀ i, FewMarkingQuery (requests i) ∧ (requests i).beta = ![1, 1, 0] := by
  unfold FewMarkingQuery
  decide +kernel

/-- The same ordinary value in different rows still belongs to distinct ordered inputs. -/
theorem requests_injective : Function.Injective requests := by
  intro i j
  exact (by decide +kernel : ∀ a b, requests a = requests b → a = b) i j

/-- The 105 rows are exactly the specified benchmark at the full class E₁+E₂. -/
theorem coverage : Finset.univ.image requests =
    (fewMarkingQueries .blowupTwo).filter (fun q ↦ q.beta = ![1, 1, 0]) := by
  apply Finset.eq_of_subset_of_card_le
  · intro q h
    rw [Finset.mem_filter, mem_fewMarkingQueries_iff]
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact hi ▸ frame i
  · have inj : Function.Injective
        (fun m ↦ (⟨2, ![1, 1, 0], m⟩ : SurfaceQuery .blowupTwo)) :=
      fun _ _ h ↦ congrArg SurfaceQuery.insertions h
    rw [fewMarkingQueries_filter_class _ (by decide +kernel) (by decide +kernel),
      Finset.card_image_of_injective _ inj, Finset.card_image_of_injective _ requests_injective,
      Finset.card_univ, Fintype.card_fin, card_dimensionShapes]
    decide +kernel

end AxiomaticGW.GKM.BlowupTwoMixedExceptional
