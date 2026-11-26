module

public import AxiomaticGW.PointTarget.DVVTermination
import all Mathlib.Data.List.Sort

/-! # Point-target reconstruction on unstable, off-degree, unsorted and repeated inputs -/

namespace AxiomaticGWTest.PointTarget.DVVTermination
open AxiomaticGW.PointTarget.DVVCalculation

/-- Each entry uses the total, automatically bounded evaluator. -/
example : number 0 [0, 0] = 0 ∧ number 0 [0, 0, 0] = 1 ∧ number 1 [0, 0, 3] = 1 / 24 ∧
    number 2 [1] = 0 ∧ number 2 [4] = 1 / 1152 := by decide +kernel

end AxiomaticGWTest.PointTarget.DVVTermination
