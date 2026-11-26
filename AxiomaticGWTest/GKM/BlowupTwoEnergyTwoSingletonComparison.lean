import AxiomaticGW.GKM.Fixtures.BlowupTwoEnergyTwoSingletonComparison

/-! # Controls for comparing a ruling before and after the second blowup -/

namespace AxiomaticGWTest.GKM.BlowupTwoEnergyTwoSingletonComparison
open AxiomaticGW.GKM BlowupTwoPositivePlaneEnergyTwoSingletons

/-- The unit discrepancy survives in the exact field, on both choices of ruling. -/
theorem distinct_unit (i : Fin 2) :
    equivariant (rulingIndex i 0) ≠ F1FiberOneMarking.equivariant 0 := by
  rw [(ruling i 0).2]
  norm_num

/-- Keeping the full target class distinguishes the two first exceptional insertions. -/
example : values (index 1 2) = -23/2880 ∧ values (index 2 2) = 1/2880 := by decide +kernel

end AxiomaticGWTest.GKM.BlowupTwoEnergyTwoSingletonComparison
