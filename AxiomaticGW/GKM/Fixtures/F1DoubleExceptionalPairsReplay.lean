/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalMarkedPairs
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1DoubleExceptionalInteriorPairs

/-! # Reconstruction of all 64 genus-two two-marked requests in class 2E on F₁ -/

@[expose] public section
namespace AxiomaticGW.GKM.F1DoubleExceptionalPairs
open SurfaceGenusTwoBlowupDescendants

open BlowupF1DoubleExceptionalInteriorPairs (index)

private theorem partition_rows : ∀ i : Fin 64, i ∈ reducedIndices ∨ ∃ j, index j = i := by
  decide +kernel

private theorem interior_binding : ∀ j : Fin 18,
    (requests (index j), values (index j)) =
      (BlowupF1DoubleExceptionalInteriorPairs.requests j,
       BlowupF1DoubleExceptionalInteriorPairs.values j) := by decide +kernel

/-- All positive-power and marked-equation cases agree with the original ordered native claims. -/
theorem accepted (i : Fin 64) : CheckedDescendant 0 (requests i) (values i) := by
  rcases partition_rows i with hi | ⟨j, rfl⟩
  · exact reduced_accepted hi
  · exact (congrArg (fun r ↦ CheckedDescendant 0 r.1 r.2) (interior_binding j)).mpr
      (.mixed (BlowupF1DoubleExceptionalInteriorPairs.accepted j))

end AxiomaticGW.GKM.F1DoubleExceptionalPairs
