/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalBoundarySplitting

/-! # Full-class and exceptional sign regressions for stabilized degree-one bridges -/

@[expose] public section
namespace AxiomaticGWTest.GKM.ExceptionalBoundaryClass
open AxiomaticGW AxiomaticGW.GKM ExceptionalBoundaryClass ExceptionalBoundaryData

/-- The same genus-zero integral does not permit interchanging the two exceptional curves. -/
theorem distinct_equal_energy :
    beta .first ≠ beta .second ∧
    SurfaceTarget.blowupTwo.effective.energy (beta .first) =
      SurfaceTarget.blowupTwo.effective.energy (beta .second) := by decide +kernel

/-- Exchanging the exceptional node labels loses the nonzero tail coefficient. -/
theorem crossed_tail :
    tailValue .first 0 (.exceptional ⟨0, by decide⟩) = -1 ∧
    tailValue .first 0 (.exceptional ⟨1, by decide⟩) = 0 ∧
    tailValue .second 0 (.exceptional ⟨0, by decide⟩) = 0 ∧
    tailValue .second 0 (.exceptional ⟨1, by decide⟩) = -1 := by decide +kernel

/-- Replacing the exceptional copairing weight by a positive one reverses the surviving sign. -/
theorem wrong_metric_sign (c : Case) :
    (1 : ℚ) * tailValue c 0 (.exceptional (own c)) ≠
      (SurfaceBasisLabel.exceptional (X := target c) (own c)).inverseWeight *
        tailValue c 0 (.exceptional (own c)) := by
  rw [(tail_support c _).1, if_pos rfl]
  norm_num [SurfaceBasisLabel.inverseWeight]

end AxiomaticGWTest.GKM.ExceptionalBoundaryClass
