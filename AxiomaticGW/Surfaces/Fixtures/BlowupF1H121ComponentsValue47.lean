/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1H121ComponentsData

/-!
# Kernel check of full F1 component 47

Every candidate value remains untrusted until its explicit kernel check.
Component labels use sortCode: unit=0, H=1, E0=2, point=3.
Selector observation-log SHA256: d8b50f7e8ec84f6e3ace9671fdf99440d1c315d4b3e8499f60b57f75c88ddb60
Candidate input SHA256: 378c173898f3fc8df177d98bc64f66e7236b40c466df177f998602b0b0f79e7f
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1H121Components
open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)

set_option maxHeartbeats 0 in
theorem component_47_computed :
    SurfaceLowGenusPointCache.componentValue .hirzebruchOne rational elliptic
      (key 47) = value 47 := by
  decide +kernel

theorem entry_47_eq : entries 47 = residualTerms (key 47) := by
  rw [← residualTermsWithPoints_eq .hirzebruchOne rational elliptic
    rational_eq elliptic_eq]
  rw [residualTermsWithPoints, if_pos (by decide +kernel),
    component_47_computed]
  rfl

end AxiomaticGW.BlowupF1H121Components
