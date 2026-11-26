/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalSingletons.FirstPower

/-! # Rational and elliptic second-cotangent vertices on the doubled exceptional axes -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalComponents.SecondPower
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache
open GenusTwoSecondUnitPairs.TwoBlowupComponents
open BlowupTwoDoubleExceptionalDivisor (beta)
open FirstPower (backend)

/-- The ten rational markings include the two inverse-metric contractions. The last
key is the elliptic point/unit vertex. Both target axes retain both exceptional states. -/
def marks (i : Fin 2) : Fin 11 → List (SurfaceInsertion X) :=
  let d : SurfaceInsertion X := ⟨.exceptional i, 0⟩
  let f : SurfaceInsertion X := ⟨.exceptional i.rev, 0⟩
  ![[u₀,u₀,p₀,p₀,u₂], [u₀,h₀,h₀,p₀,u₂], [u₀,d,d,p₀,u₂], [u₀,f,f,p₀,u₂],
    [h₀,h₀,h₀,h₀,u₂], [h₀,h₀,d,d,u₂], [h₀,h₀,f,f,u₂], [d,d,d,d,u₂],
    [d,d,f,f,u₂], [f,f,f,f,u₂], [p₀,u₂]]

/-- Original genus, full class and multiset of markings for each of the eleven rows. -/
def key (i : Fin 2) (j : Fin 11) : SurfaceAncestorKey X :=
  componentKey (if j = 10 then 1 else 0) (beta i) (marks i j)
    (by fin_cases i <;> fin_cases j <;> decide +kernel)

/-- Only the four own primary divisors with the second unit ancestor contribute. -/
def values (j : Fin 11) : ℚ := if j = 7 then -1 else 0

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000 in
-- Replay the lower-genus cotangent equation for each dimension-compatible marked vertex.
/-- Each indexed value satisfies its original lower-genus cotangent equation. -/
theorem accepted (i : Fin 2) (j : Fin 11) :
    values j = stagedValue backend.value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- All 22 second-cotangent values, each carrying its checked boundary equation. -/
def rows (i : Fin 2) : List (Entry X) :=
  (List.finRange 11).map fun j ↦ backend.entry (key i j) (values j) (accepted i j)

/-- The second layer uses the preceding first-cotangent and lower-class records. -/
def second : CertifiedComponents X := addRows backend 2 rows

end AxiomaticGW.BlowupTwoDoubleExceptionalComponents.SecondPower
