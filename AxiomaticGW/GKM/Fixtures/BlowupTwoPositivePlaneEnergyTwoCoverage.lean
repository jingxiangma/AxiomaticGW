/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoReplay
public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleLinePointPairReplay

/-! # Ordered energy-two pair rows with a target-side proof on a positive-plane class -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoPositivePlaneEnergyTwoPairs
open SurfaceGenusTwoBlowupDescendants EquivariantCoefficients
open BlowupTwoDoubleLinePairs (index pointIndex point_certified)

/-- Marked reductions together with the sixteen interior strict-line point descendants. -/
def verifiedRows : Finset (Fin 300) :=
  markedRows ∪ Finset.univ.image (fun t : Fin 8 × Bool ↦ index (pointIndex t.1 t.2))

/-- Full-coordinate counts in the order 2L, E₂ + L, E₁ + L. -/
theorem verified_counts : verifiedRows.card = 166 ∧ ∀ c : Fin 3,
    (verifiedRows.filter (fun j ↦
      (requests j).beta = BlowupTwoPositivePlaneEnergyTwoSingletons.curves c)).card =
      ![66,50,50] c := by decide +kernel

/-- Original reconstruction witness for every verified ordered pair. -/
theorem verified_accepted {j : Fin 300} (h : j ∈ verifiedRows) :
    CheckedDescendant 0 (requests j) (values j) := by
  rcases Finset.mem_union.mp h with hm | hp
  · exact marked_accepted hm
  · obtain ⟨⟨a, last⟩, _, rfl⟩ := Finset.mem_image.mp hp
    exact .mixed (point_certified a last).1

/-- The original arithmetic proof and the full incoming field on the same ordered row. -/
theorem verified_certified {j : Fin 300} (h : j ∈ verifiedRows) :
    CheckedDescendant 0 (requests j) (values j) ∧ equivariant j = (values j : Coefficient) ∧
      Specializes (equivariant j) (values j) :=
  ⟨verified_accepted h, equivariant_eq_ordinary j, specializes j⟩

end AxiomaticGW.GKM.BlowupTwoPositivePlaneEnergyTwoPairs
