/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberHZeroCoefficients

@[expose] public section
set_option maxRecDepth 20000

namespace AxiomaticGW.BlowupF1FiberHZeroValues
open BlowupF1FiberHZeroCoefficients

/-- Exact original weighted contribution at held index 101; no term omitted. -/
theorem k_0101 : weightedTerm (.exceptional 0) 101 = ((4 / 3 : ℚ) : ℚ) := by
  decide +kernel

end AxiomaticGW.BlowupF1FiberHZeroValues
