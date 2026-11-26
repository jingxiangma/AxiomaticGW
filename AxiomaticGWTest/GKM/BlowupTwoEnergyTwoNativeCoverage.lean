/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoEnergyTwoNativeCoverage
public import AxiomaticGW.GKM.Fixtures.F1FiberOneMarkingReplay

/-! # Query-level checks on the energy-two localization references -/

@[expose] public section
namespace AxiomaticGWTest.GKM.BlowupTwoEnergyTwoNativeCoverage
open AxiomaticGW AxiomaticGW.GKM EquivariantCoefficients
open AxiomaticGW.GKM.BlowupTwoEnergyTwoNativeCoverage

/-- The unit descendant at the ruling E₂+L and at the F₁ fiber gives two different
full-field coefficients with their standard target restrictions. -/
theorem ruling_unit :
    let r : Row := .inr (.inr (.inl 5))
    lookup ⟨2, ![0, 1, 1], [⟨.unit, 4⟩]⟩ = some r ∧
      F1FiberOneMarking.requests 0 = ⟨2, ![0, 1], [⟨.unit, 4⟩]⟩ ∧
      equivariant r = ((-9 / 640 : ℚ) : Coefficient) ∧
      F1FiberOneMarking.equivariant 0 = ((-1 / 120 : ℚ) : Coefficient) ∧
      equivariant r ≠ F1FiberOneMarking.equivariant 0 := by
  dsimp only
  refine ⟨(lookup_eq_some_iff _ _).mpr (by decide +kernel), by decide +kernel, ?_⟩
  rw [equivariant_eq_ordinary, F1FiberOneMarking.equivariant_eq_ordinary,
    show values (.inr (.inr (.inl 5))) = -9/640 by decide +kernel,
    show F1FiberOneMarking.values 0 = -1/120 by decide +kernel]
  exact ⟨rfl, rfl, by norm_num⟩

/-- Exchanging the two powers preserves their labels and total dimension but changes
the row of the strict-line double-cover report. Both fractions equal 27/1280. -/
theorem ordered_pair :
    lookup ⟨2, ![0, 0, 2], [⟨.unit, 2⟩, ⟨.unit, 3⟩]⟩ = some (.inr (.inr (.inr 2))) ∧
    lookup ⟨2, ![0, 0, 2], [⟨.unit, 3⟩, ⟨.unit, 2⟩]⟩ = some (.inr (.inr (.inr 3))) ∧
    equivariant (.inr (.inr (.inr 2))) = ((27 / 1280 : ℚ) : Coefficient) ∧
    equivariant (.inr (.inr (.inr 3))) = ((27 / 1280 : ℚ) : Coefficient) := by
  refine ⟨(lookup_eq_some_iff _ _).mpr (by decide +kernel),
    (lookup_eq_some_iff _ _).mpr (by decide +kernel), ?_⟩
  rw [equivariant_eq_ordinary, equivariant_eq_ordinary,
    show values (.inr (.inr (.inr 2))) = 27/1280 by decide +kernel,
    show values (.inr (.inr (.inr 3))) = 27/1280 by decide +kernel]
  exact ⟨rfl, rfl⟩

/-- Altering just the last power violates the dimension condition. -/
theorem wrong_dimension :
    lookup ⟨2, ![0, 0, 2], [⟨.unit, 2⟩, ⟨.unit, 2⟩]⟩ = none := by decide +kernel

end AxiomaticGWTest.GKM.BlowupTwoEnergyTwoNativeCoverage
