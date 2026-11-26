/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalInteriorPairs.Reduction

/-! # Point-free two-marked interior descendants in class E₁ + E₂ on Bl₂

The thirty-two ordered requests avoid the string, dilaton and primary divisor
reductions. Their original mixed calibration uses square relations over all
four effective subcurves, primitive divisor products and low-power terminals.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- All 44 ancestors appearing in the original mixed expansion vanish. -/
theorem ancestor_values (j : Fin 44) : SurfaceGenusTwo.ancestorValue low (key j) = 0 := by
  refine Fin.addCases (m := 28) (n := 16) (fun i ↦ ?_) (fun i ↦ ?_) j
  · simpa only [key, Fin.addCases_left] using square_values i
  · simp only [key, Fin.addCases_right]
    refine Fin.addCases (m := 6) (n := 10) (fun k ↦ ?_) (fun k ↦ ?_) i
    · simpa only [Fin.addCases_left] using product_values k
    · simpa only [Fin.addCases_right] using low_values k

/-- The ordered descendant values in the point-free interior of the full 100-row pair frame. -/
def values : Fin 32 → ℚ := 0

/-- Every original mixed reconstruction on this complete interior frame returns zero. -/
theorem accepted (j : Fin 32) : queryValue? 0 (requests j) = some (values j) := by
  simpa only [fullAncestor, square_values, values, Pi.zero_apply] using query_full_square j

end AxiomaticGW.BlowupTwoMixedExceptionalInteriorPairs
