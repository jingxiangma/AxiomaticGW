/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoF1PositivePairs
public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneSelection
public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneCoverage
public import AxiomaticGW.GKM.Fixtures.GenusTwoEnergyOneEquivariant

/-! # All 52 energy-one genus-two few-marking requests on the first blowup

Each native row agrees with a reconstruction of its original ordered insertions.
Coverage is stated for the mathematical query set, independently of the exporter order.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoEnergyOne
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

namespace OneBlowup

private theorem selected_accepted (s : Fin 43 ⊕ (Fin 3 × Fin 3)) :
    CheckedDescendant 0 (selectedRow s).1 (selectedRow s).2 := by
  rcases s with i | ⟨a, b⟩
  · exact reductions_accepted i
  · exact .mixed (GenusTwoPositivePairs.OneBlowup.all_accepted a b)

/-- Reconstruction verifies each of the 52 native ordinary specializations on the exceptional. -/
theorem accepted (i : Fin 52) : CheckedDescendant 0 (requests i) (values i) := by
  have h := selected_accepted (selection i)
  rwa [selection_matches i] at h

/-- Every ordered energy-one benchmark request on the first blowup has a certified native row. -/
theorem certified_of_mem {q : SurfaceQuery .hirzebruchOne}
    (hq : q ∈ fewMarkingsAtEnergy .hirzebruchOne 1) :
    ∃ i, requests i = q ∧ CheckedDescendant 0 q (values i) := by
  rw [← coverage] at hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨i, rfl, accepted i⟩

/-- A benchmark request has a unique row matching its reconstruction and native fraction. -/
theorem unique_comparison {q : SurfaceQuery .hirzebruchOne}
    (hq : q ∈ fewMarkingsAtEnergy .hirzebruchOne 1) :
    ∃! i, requests i = q ∧ CheckedDescendant 0 q (values i) ∧
      EquivariantCoefficients.Specializes (equivariant i) (values i) := by
  obtain ⟨i, hi, hv⟩ := certified_of_mem hq
  refine ⟨i, ⟨hi, hv, specializes i⟩, ?_⟩
  intro j hj
  exact requests_injective (hj.1.trans hi.symm)

end OneBlowup
end AxiomaticGW.GKM.GenusTwoEnergyOne
