/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoMixedExceptionalReplay
public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction

/-! # Genus-two GW vanishing in class E₁+E₂ at up to two arbitrary descendant powers -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoMixedExceptional
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- A dimension-compatible ordered request in this class has a checked zero witness. -/
theorem compatible_zero (q : SurfaceQuery .blowupTwo) (hg : q.genus = 2)
    (hb : q.beta = ![1, 1, 0]) (hn : q.insertions.length ≤ 2) (hd : q.DimensionCompatible) :
    CheckedDescendant 0 q 0 := by
  have hne : q.beta ≠ 0 := by rw [hb]; decide +kernel
  have he : SurfaceTarget.blowupTwo.effective.energy q.beta ≤ 4 := by rw [hb]; decide +kernel
  obtain ⟨_, h, _⟩ := unique_comparison ⟨hg, hne, he, hn, hd⟩ hb
  exact h.2.1

/-- For every ordered list of at most two basis descendants in class E₁+E₂ the ordinary
genus-two GW value is zero under the original geometric reconstruction inputs.
The cotangent powers have no bound. -/
theorem all_powers_from_geometry (q : SurfaceQuery .blowupTwo) (hg : q.genus = 2)
    (hb : q.beta = ![1, 1, 0]) (hn : q.insertions.length ≤ 2) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedZero_from_geometry
    (X := .blowupTwo) (i := 0) (q := q) (hg := hg) (h := compatible_zero q hg hb hn)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedZero_from_geometry
    (X := .blowupTwo) (i := 0) (q := q) (hg := hg) (h := compatible_zero q hg hb hn)

/-- The same vanishing holds for arbitrary surface cohomology insertions on a finite marking
type of cardinality at most two, with the original geometric reconstruction hypotheses. -/
theorem arbitrary_states_from_geometry (S : Type) [Fintype S] (hS : Fintype.card S ≤ 2)
    (k : S → ℕ) (a : S → SurfaceCohomology 2) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.stateZero_from_geometry
      (X := .blowupTwo) (i := 0) (S := S) (beta := ![1, 1, 0]) (k := k) (a := a)
      (h := fun q hg hb hn ↦ compatible_zero q hg hb (hn.trans_le hS))) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.stateZero_from_geometry
      (X := .blowupTwo) (i := 0) (S := S) (beta := ![1, 1, 0]) (k := k) (a := a)
      (h := fun q hg hb hn ↦ compatible_zero q hg hb (hn.trans_le hS))

end AxiomaticGW.GKM.BlowupTwoMixedExceptional
