/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.DivisorPointSources

/-! # Original divisor-square and primary-point rows at the two rulings -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingDivisorPoint
open BlowupTwoRuling (X)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- Signed pulled-square values in correction-first order. -/
def squareParts (j : Fin 3) : Fin 11 → ℚ := if j = 1 then 0 else
  ![-1/1440, 155/50544, 35/25272, 23/56160, 0, 0, 0, 0, 0, 0, 0]

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 4000000 in
-- Each full ruling and each absolute marking is contracted graph by graph.
/-- All six complete eleven-source pulled squares use the original backend. -/
theorem square_parts (i : Fin 2) (j : Fin 3) (n : Fin 11) :
    squareSource i j n = squareParts j n := by
  fin_cases i <;> fin_cases j <;> fin_cases n <;> decide +kernel

/-- Twelve ordered descendants follow from the full original pulled-square and calibration. -/
theorem square_accepted (i : Fin 2) (j : Fin 3) (pointFirst : Bool) :
    queryValue? 0 (request i j true pointFirst) = some (if j = 1 then 0 else 1/240) := by
  rw [query_eq_leading, square_sum]
  simp only [square_parts]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupTwoRulingDivisorPoint
