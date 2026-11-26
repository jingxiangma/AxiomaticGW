/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1EnergyTwoCoverage
public import AxiomaticGW.GKM.Fixtures.F1FiberPairsReplay
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalPairsReplay

/-! # Certified genus-two descendants at anticanonical energy two on F₁

The two curve classes have the same dimension-compatible ordered insertion lists.
The full class in every row distinguishes the fiber from twice the exceptional curve.
-/

@[expose] public section
namespace AxiomaticGW.GKM.F1EnergyTwo
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Value reported by localization in ordinary cohomology. -/
def value : Row → ℚ :=
  Sum.elim F1Fiber.value
    (Sum.elim F1DoubleExceptionalOneMarking.values F1DoubleExceptionalPairs.values)

/-- The fraction in both torus characters with its incoming numerator and denominator. -/
noncomputable def equivariant : Row → EquivariantCoefficients.Coefficient :=
  Sum.elim F1Fiber.equivariant
    (Sum.elim F1DoubleExceptionalOneMarking.equivariant F1DoubleExceptionalPairs.equivariant)

/-- The arithmetic proof, full-field comparison and regular specialization use one row. -/
theorem accepted (i : Row) : CheckedDescendant 0 (request i) (value i) ∧
    equivariant i = (value i : EquivariantCoefficients.Coefficient) ∧
    EquivariantCoefficients.Specializes (equivariant i) (value i) := by
  rcases i with (i | i) | (i | i)
  · exact ⟨.mixed (F1FiberOneMarking.accepted i),
      F1FiberOneMarking.equivariant_eq_ordinary i, F1FiberOneMarking.specializes i⟩
  · exact ⟨F1FiberPairs.accepted i, F1FiberPairs.equivariant_eq_ordinary i,
      F1FiberPairs.specializes i⟩
  · exact ⟨.mixed (F1DoubleExceptionalOneMarking.accepted i),
      F1DoubleExceptionalOneMarking.equivariant_eq_ordinary i,
      F1DoubleExceptionalOneMarking.specializes i⟩
  · exact ⟨F1DoubleExceptionalPairs.accepted i, F1DoubleExceptionalPairs.equivariant_eq_ordinary i,
      F1DoubleExceptionalPairs.specializes i⟩

/-- Every mathematical benchmark request has a unique native and reconstructed comparison. -/
theorem unique_comparison {q : SurfaceQuery .hirzebruchOne}
    (hq : q ∈ fewMarkingsAtEnergy .hirzebruchOne 2) : ∃! i, request i = q ∧
      CheckedDescendant 0 q (value i) ∧
      equivariant i = (value i : EquivariantCoefficients.Coefficient) ∧
      EquivariantCoefficients.Specializes (equivariant i) (value i) := by
  rw [← coverage] at hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨i, ⟨rfl, accepted i⟩, fun j hj ↦ requests_injective hj.1⟩

end AxiomaticGW.GKM.F1EnergyTwo
