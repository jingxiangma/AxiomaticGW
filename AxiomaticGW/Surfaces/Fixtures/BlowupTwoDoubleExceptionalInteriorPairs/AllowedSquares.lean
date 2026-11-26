/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Fourth

/-! # The four surviving doubled exceptional two-marked ancestor squares -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
open SurfaceGenusTwo

/-- The only four square profiles permitted by the support of a doubled exceptional axis. -/
def allowedSquare : Fin 4 → Fin 16 := ![5,7,13,15]

/-- All eleven signed graph contributions, including the exceptional-plus-exceptional splitting. -/
def signedParts (r : Fin 4) (g : Fin 11) : ℚ :=
  let table : Fin 4 → Fin 11 → ℚ :=
    ![![0, -775/101088, -175/50544, -23/44928, 41/71604,
        -7/4212, -31/2106, -749/168480, -101/5728320, -1/1664,
        -7/56160],
      ![0, 155/50544, 35/25272, 0, -205/143208,
        7/3744, 31/2592, 0, 101/2291328, 1/2080,
        1/6240],
      ![0, 155/67392, 35/33696, 23/112320, -41/71604,
        35/33696, 31/2808, 749/84240, 101/5728320, 1/8320,
        1/18720],
      ![0, 0, 0, 0, 41/143208,
        -7/22464, -31/11232, -749/336960, -101/11456640, 0,
        -1/56160]]
  table r g

set_option maxRecDepth 65536
set_option Elab.async false

set_option maxHeartbeats 6000000 in
-- Each graph retains all effective splittings and its signed inverse-metric contraction.
/-- The original eleven graph sources have the indicated values on either full curve class. -/
theorem allowed_parts (i : Fin 2) (r : Fin 4) (g : Fin 11) :
    squarePart (Fourth.backend i) i (allowedSquare r) g = signedParts r g := by
  fin_cases i <;> fin_cases r <;> fin_cases g <;> decide +kernel

/-- All sixteen candidate square values before combining the calibrated tails. -/
def squareValues : Fin 16 → ℚ :=
  ![0, 0, 0, 0, 0, -47/1440, 0, 101/5760, 0, 0, 0, 0, 0, 139/5760, 0, -29/5760]

theorem allowed_values (i : Fin 2) (r : Fin 4) :
    ancestorValue low (squareKey i (allowedSquare r)) = squareValues (allowedSquare r) := by
  rw [square_sum (Fourth.backend i)]
  simp only [allowed_parts]
  fin_cases r <;> decide +kernel

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs
