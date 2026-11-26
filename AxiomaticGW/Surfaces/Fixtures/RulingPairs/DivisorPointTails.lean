/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.DivisorPointFrame

/-! # Proper calibrated divisor–point terms on the two rulings of Bl₂ -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingDivisorPoint
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleLine (terminals)

/-- The original low-power genus-two base with previously certified primitive rows. -/
abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals

set_option maxRecDepth 65536

/-- All twenty-one proper-class ancestors in the divisor–point calibration vanish. -/
theorem tail_values (i : Fin 2) (r : Fin 21) :
    ancestorValueWith terminals (tailKey i r) = 0 := by
  change ancestorValue low (tailKey i r) = 0
  fin_cases i <;> fin_cases r <;>
    rw [ancestorValue_low low _ rfl (by decide +kernel)] <;> decide +kernel

/-- At these 24 ordered requests the signed proper terms leave the leading ancestor unchanged. -/
theorem query_eq_leading (i : Fin 2) (j : Fin 3) (square pointFirst : Bool) :
    queryValue? 0 (request i j square pointFirst) =
      some (ancestorValue low (leading i j square)) := by
  rw [query_eq]
  simp only [tail_values, mul_zero, List.map_const', List.sum_replicate, nsmul_zero, add_zero]
  rfl

end AxiomaticGW.BlowupTwoRulingDivisorPoint
