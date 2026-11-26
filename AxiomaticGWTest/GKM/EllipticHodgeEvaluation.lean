module

public import AxiomaticGW.GKM.EllipticHodgeEvaluation
import all Mathlib.Data.List.Sort

/-! # Three-marked genus-one surface vertex Hodge integrals -/

namespace AxiomaticGWTest.GKM.EllipticHodgeEvaluation
open AxiomaticGW.GKM.EllipticHodge

/-- The original GKM producer gives the same five values for these marking and Hodge profiles. -/
example : nativeMoment 0 1 ![0,1,1] = 1 / 12 ∧ nativeMoment 1 0 ![2,0,0] = 1 / 24 ∧
    nativeMoment 1 1 ![0,0] = 0 ∧ nativeMoment 0 1 ![0,0,0] = 0 ∧
    nativeMoment 0 0 ![0,0,3] = 1 / 24 := by decide +kernel

end AxiomaticGWTest.GKM.EllipticHodgeEvaluation
