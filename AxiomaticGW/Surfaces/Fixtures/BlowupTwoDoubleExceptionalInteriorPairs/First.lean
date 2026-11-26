/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Components

/-! # Cotangent-degree 1 components of the doubled exceptional interior squares -/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs.First
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache MarkedVertex
open BlowupTwoDoubleExceptionalDivisor (beta)

/-- Each key retains its genus, full effective curve, basis states and cotangent powers. -/
def key (i : Fin 2) (j : Fin 29) : SurfaceAncestorKey X :=
  (#[node 0 0 [unit 0, unit 0, hyperplane 0, hyperplane 0, hyperplane 1],
    node 0 0 [unit 0, unit 0, hyperplane 0, hyperplane 1],
    node 0 0 [unit 0, unit 0, divisor i 0, divisor i 0, divisor i 1],
    node 0 0 [unit 0, unit 0, divisor i 0, divisor i 1],
    node 0 0 [unit 0, unit 0, divisor i.rev 0, divisor i.rev 0, divisor i.rev 1],
    node 0 0 [unit 0, unit 0, divisor i.rev 0, divisor i.rev 1],
    node 0 0 [unit 0, unit 0, point 0, unit 1],
    node 0 0 [unit 0, hyperplane 0, hyperplane 0, unit 1],
    node 0 0 [unit 0, divisor i 0, divisor i 0, unit 1],
    node 0 0 [unit 0, divisor i.rev 0, divisor i.rev 0, unit 1],
    node 0 (X.exceptionalCurve i) [unit 0, divisor i 0, divisor i 0, divisor i 0, divisor i 1],
    node 0 (X.exceptionalCurve i) [unit 0, divisor i 0, divisor i 0, divisor i 1],
    node 0 (X.exceptionalCurve i) [divisor i 0, divisor i 0, divisor i 0, unit 1],
    node 0 (beta i) [divisor i 0, divisor i 0, divisor i 0, divisor i 0, divisor i 0, divisor i 1],
    node 0 (beta i) [divisor i 0, divisor i 0, divisor i 0, divisor i 0, divisor i 1],
    node 0 (beta i) [divisor i 0, divisor i 0, divisor i 0, divisor i 1],
    node 1 0 [unit 0, hyperplane 0, hyperplane 1],
    node 1 0 [unit 0, divisor i 0, divisor i 1],
    node 1 0 [unit 0, divisor i.rev 0, divisor i.rev 1],
    node 1 0 [unit 0, hyperplane 1],
    node 1 0 [unit 0, divisor i 1],
    node 1 0 [unit 0, divisor i.rev 1],
    node 1 0 [hyperplane 0, unit 1],
    node 1 0 [divisor i 0, divisor i 0, unit 1],
    node 1 0 [divisor i 0, unit 1],
    node 1 0 [divisor i.rev 0, unit 1],
    node 1 (X.exceptionalCurve i) [divisor i 0, divisor i 0, divisor i 1],
    node 1 (X.exceptionalCurve i) [divisor i 0, divisor i 1],
    node 1 (X.exceptionalCurve i) [divisor i 1]] :
    Array (SurfaceAncestorKey X))[j.val]'j.isLt

/-- Lower-genus values for the complete marked keys at this degree. -/
def values (j : Fin 29) : ℚ :=
  (#[0, 1, 0, -1, 0, -1, 1, 1, -1, -1,
    1, -1, -1, -7, 3, -1, 0, 0, 0, -1/8,
    -1/24, -1/24, -1/8, 0, -1/24, -1/24, 1/12, -1/12, 1/24] : Array ℚ)[j.val]'j.isLt

set_option Elab.async false
set_option maxRecDepth 65536

set_option maxHeartbeats 2500000 in
-- Each marked vertex is replayed through the immediately preceding cotangent degree.
/-- The displayed values satisfy the original staged cotangent recursion at every key. -/
theorem accepted (i : Fin 2) (j : Fin 29) :
    values j = stagedValue initial.value (key i j) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Certified component evaluator through cotangent degree 1 on the given exceptional chart. -/
def backend (i : Fin 2) : CertifiedComponents X :=
  componentLayer initial 1 ((List.finRange 29).map fun j ↦
    initial.entry (key i j) (values j) (accepted i j))

end AxiomaticGW.BlowupTwoDoubleExceptionalInteriorPairs.First
