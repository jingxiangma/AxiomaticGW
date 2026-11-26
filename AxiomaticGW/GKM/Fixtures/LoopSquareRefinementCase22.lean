/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementData

/-! One of the twelve unchanged finite classification checks. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSquareRefinements

theorem classification_case_2_2 : classificationCheck 2 2 = true := by
  simp only [classificationCheck, StableGraphCode.candidates_eq_standard,
    StableGraphCode.standardCandidates]
  decide +kernel

end AxiomaticGW.GKM.LoopSquareRefinements
