/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.First

/-! # Cotangent-degree 2 components of the doubled exceptional interior squares -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs.Second
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache MarkedVertex
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- Each key retains its genus, full effective curve, basis states and cotangent powers. -/
def key (i : Fin 2) (j : Fin 33) : SurfaceAncestorKey X :=
  (#[node 0 0 [unit 0, unit 0, unit 0, point 0, unit 2],
    node 0 0 [unit 0, unit 0, hyperplane 0, hyperplane 0, unit 2],
    node 0 0 [unit 0, unit 0, divisor i 0, divisor i 0, unit 2],
    node 0 0 [unit 0, unit 0, divisor i.rev 0, divisor i.rev 0, unit 2],
    node 0 (X.exceptionalCurve i) [unit 0, unit 0, divisor i 0, divisor i 0, divisor i 2],
    node 0 (X.exceptionalCurve i) [unit 0, divisor i 0, divisor i 0, divisor i 0, unit 2],
    node 0 (X.exceptionalCurve i) [unit 0, divisor i 0, divisor i 0, unit 1, divisor i 1],
    node 0 (beta i) [unit 0, divisor i 0, divisor i 0, divisor i 0, divisor i 0, divisor i 2],
    node 0 (beta i) [unit 0, divisor i 0, divisor i 0, divisor i 0, divisor i 1, divisor i 1],
    node 0 (beta i) [unit 0, divisor i 0, divisor i 0, divisor i 0, divisor i 2],
    node 0 (beta i) [unit 0, divisor i 0, divisor i 0, divisor i 1, divisor i 1],
    node 0 (beta i) [divisor i 0, divisor i 0, divisor i 0, divisor i 0, unit 1, divisor i 1],
    node 0 (beta i) [divisor i 0, divisor i 0, divisor i 0, divisor i 0, unit 2],
    node 0 (beta i) [divisor i 0, divisor i 0, divisor i 0, unit 1, divisor i 1],
    node 1 0 [unit 0, unit 0, hyperplane 2],
    node 1 0 [unit 0, unit 0, divisor i 2],
    node 1 0 [unit 0, unit 0, divisor i.rev 2],
    node 1 0 [unit 0, unit 1, hyperplane 1],
    node 1 0 [unit 0, unit 1, divisor i 1],
    node 1 0 [unit 0, unit 1, divisor i.rev 1],
    node 1 0 [unit 0, unit 2],
    node 1 0 [unit 1, unit 1],
    node 1 (X.exceptionalCurve i) [unit 0, divisor i 0, divisor i 2],
    node 1 (X.exceptionalCurve i) [unit 0, divisor i 1, divisor i 1],
    node 1 (X.exceptionalCurve i) [unit 0, divisor i 2],
    node 1 (X.exceptionalCurve i) [divisor i 0, unit 1, divisor i 1],
    node 1 (X.exceptionalCurve i) [divisor i 0, unit 2],
    node 1 (X.exceptionalCurve i) [unit 1, divisor i 1],
    node 1 (beta i) [divisor i 0, divisor i 0, divisor i 1, divisor i 1],
    node 1 (beta i) [divisor i 0, divisor i 0, divisor i 2],
    node 1 (beta i) [divisor i 0, divisor i 1, divisor i 1],
    node 1 (beta i) [divisor i 0, divisor i 2],
    node 1 (beta i) [divisor i 1, divisor i 1]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Lower-genus values for the complete marked keys at this degree. -/
def values (j : Fin 33) : ℚ :=
  (#[1, 1, -1, -1, -1, -1, -2, 3, 6, -1,
    -2, 9, -1, -2, -1/8, -1/24, -1/24, -1/4, -1/12, -1/12,
    5/24, 5/24, -1/12, -1/6, 1/24, -1/6, 1/24, 1/24, 2/3, -1/6,
    -1/4, 1/24, 1/24] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 2500000 in
-- Each marked vertex is replayed through the immediately preceding cotangent degree.
/-- The displayed values satisfy the original staged cotangent recursion at every key. -/
theorem accepted (i : Fin 2) (j : Fin 33) :
    values j = stagedValue (First.backend i).value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Certified component evaluator through cotangent degree 2 on the given exceptional chart. -/
def backend (i : Fin 2) : CertifiedComponents X :=
  componentLayer (First.backend i) 2 ((List.finRange 33).map fun j ↦
    (First.backend i).entry (key i j) (values j) (accepted i j))

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs.Second
