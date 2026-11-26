/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeExternalPsi

/-! Public checks retain the square coefficient, mixed multiplicities and all 28 positions. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGWTest.GKM.HodgeExternalPsi

open AxiomaticGW AxiomaticGW.GKM.HodgeExternalPsi
open AxiomaticGW.AdmcyclesHodgeStrataCandidates

/-- The square occurs once, while psi-kappa and each psi-boundary term occur twice. -/
theorem exact_target_weights :
    raw_1_1_degree2Coordinates 15 = (1 / 144 : ℚ) ∧
      raw_1_1_degree2Coordinates 9 = (-1 / 72 : ℚ) ∧
      raw_1_1_degree2Coordinates 0 = (-1 / 144 : ℚ) ∧
      raw_1_1_degree2Coordinates 1 = (-1 / 144 : ℚ) ∧
      raw_1_1_degree2Coordinates 2 = (-1 / 144 : ℚ) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every remainder index is distinct. -/
theorem remainder_injective : Function.Injective remainderIndices := by
  decide +kernel

/-- No external-psi target is silently duplicated in the remainder. -/
theorem remainder_excludes_psi :
    ∀ i, remainderIndices i ≠ 0 ∧ remainderIndices i ≠ 1 ∧ remainderIndices i ≠ 2 ∧
      remainderIndices i ≠ 9 ∧ remainderIndices i ≠ 15 := by
  decide +kernel

/-- The five explicitly handled positions and the remainder cover the original frame. -/
theorem full_position_coverage :
    ∀ j : Fin 28, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 9 ∨ j = 15 ∨
      ∃ i, remainderIndices i = j := by
  decide +kernel

end AxiomaticGWTest.GKM.HodgeExternalPsi
