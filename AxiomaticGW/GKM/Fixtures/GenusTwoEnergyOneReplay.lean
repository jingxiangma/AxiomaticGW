/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoAllPositivePairs
public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneF1Replay

/-! # Genus-two reconstruction of the energy-one few-marking benchmark

Each native row agrees with a reconstruction of its original ordered insertions.
Coverage is stated for the mathematical query set, independently of the exporter order.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoEnergyOne
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

namespace TwoBlowups

private theorem selected_accepted (s : Fin 192 ⊕ (Fin 3 × Fin 4 × Fin 4)) :
    CheckedDescendant 0 (selectedRow s).1 (selectedRow s).2 := by
  rcases s with i | ⟨c, a, b⟩
  · exact reductions_accepted i
  · fin_cases c
    · exact .mixed (GenusTwoPositivePairs.ExceptionalOne.all_accepted a b)
    · exact .mixed (GenusTwoPositivePairs.ExceptionalTwo.all_accepted a b)
    · exact .mixed (GenusTwoPositivePairs.StrictLine.all_accepted a b)

/-- Reconstruction verifies each of the 240 native ordinary specializations on the second blowup. -/
theorem accepted (i : Fin 240) : CheckedDescendant 0 (requests i) (values i) := by
  have h := selected_accepted (selection i)
  rwa [selection_matches i] at h

/-- Each request on either exceptional or their strict line has a certified native row. -/
theorem certified_of_mem {q : SurfaceQuery .blowupTwo}
    (hq : q ∈ fewMarkingsAtEnergy .blowupTwo 1) :
    ∃ i, requests i = q ∧ CheckedDescendant 0 q (values i) := by
  rw [← coverage] at hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨i, rfl, accepted i⟩

/-- A benchmark request has a unique row matching its reconstruction and native fraction. -/
theorem unique_comparison {q : SurfaceQuery .blowupTwo}
    (hq : q ∈ fewMarkingsAtEnergy .blowupTwo 1) :
    ∃! i, requests i = q ∧ CheckedDescendant 0 q (values i) ∧
      EquivariantCoefficients.Specializes (equivariant i) (values i) := by
  obtain ⟨i, hi, hv⟩ := certified_of_mem hq
  refine ⟨i, ⟨hi, hv, specializes i⟩, ?_⟩
  intro j hj
  exact requests_injective (hj.1.trans hi.symm)

end TwoBlowups
end AxiomaticGW.GKM.GenusTwoEnergyOne
