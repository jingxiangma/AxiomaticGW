/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Transfer

/-! # Low-power terminals for the two-marked F₁ fiber calculation -/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- All nine low-power terminals have zero reconstructed value. -/
theorem low_values (j : Fin 9) : SurfaceGenusTwo.ancestorValue low (lowKey j) = 0 := by
  rw [ancestorValue_low low _ (by fin_cases j <;> rfl) (by fin_cases j <;> decide +kernel)]
  fin_cases j <;> decide +kernel

/-- The two orders of the primary point and its first descendant, manifest positions 62 and 63. -/
theorem point_pair (j : Fin 2) :
    queryValue? 0 (requests ((![30, 31] : Fin 2 → Fin 32) j)) = some 0 := by
  rw [query_from_ancestors]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1FiberInteriorPairs
