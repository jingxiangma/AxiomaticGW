/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Third

/-! # Cotangent-degree 4 components of the doubled exceptional interior squares -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs.Fourth
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache MarkedVertex
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- Each key retains its genus, full effective curve, basis states and cotangent powers. -/
def key (i : Fin 2) (j : Fin 2) : SurfaceAncestorKey X :=
  (#[node 1 (beta i) [unit 0, divisor i 0, divisor i 1, unit 3],
    node 1 (beta i) [divisor i 0, divisor i 0, unit 1, unit 3]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Lower-genus values for the complete marked keys at this degree. -/
def values (j : Fin 2) : ℚ :=
  (#[1/8, 1/8] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 2500000 in
-- Each marked vertex is replayed through the immediately preceding cotangent degree.
/-- The displayed values satisfy the original staged cotangent recursion at every key. -/
theorem accepted (i : Fin 2) (j : Fin 2) :
    values j = stagedValue (Third.backend i).value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Certified component evaluator through cotangent degree 4 on the given exceptional chart. -/
def backend (i : Fin 2) : CertifiedComponents X :=
  componentLayer (Third.backend i) 4 ((List.finRange 2).map fun j ↦
    (Third.backend i).entry (key i j) (values j) (accepted i j))

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs.Fourth
