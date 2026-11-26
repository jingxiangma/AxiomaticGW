/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0175Data

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay.Representative0175

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

theorem fundamental_eq :
    fundamentalPart certifiedCache 175 =
      fundamentalClaim := by
  decide +kernel

theorem separating_0_unit_0 :
    separatingPart certifiedCache 175 0 .unit 0 =
      separatingClaim 0 .unit 0 := by
  decide +kernel

theorem separating_0_unit_1 :
    separatingPart certifiedCache 175 0 .unit 1 =
      separatingClaim 0 .unit 1 := by
  decide +kernel

theorem separating_0_hyperplane_0 :
    separatingPart certifiedCache 175 0 .hyperplane 0 =
      separatingClaim 0 .hyperplane 0 := by
  decide +kernel

theorem separating_0_hyperplane_1 :
    separatingPart certifiedCache 175 0 .hyperplane 1 =
      separatingClaim 0 .hyperplane 1 := by
  decide +kernel

theorem separating_0_exceptional_0 :
    separatingPart certifiedCache 175 0 (.exceptional 0) 0 =
      separatingClaim 0 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_0_exceptional_1 :
    separatingPart certifiedCache 175 0 (.exceptional 0) 1 =
      separatingClaim 0 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_0_point_0 :
    separatingPart certifiedCache 175 0 .point 0 =
      separatingClaim 0 .point 0 := by
  decide +kernel

theorem separating_0_point_1 :
    separatingPart certifiedCache 175 0 .point 1 =
      separatingClaim 0 .point 1 := by
  decide +kernel

theorem separating_1_unit_0 :
    separatingPart certifiedCache 175 1 .unit 0 =
      separatingClaim 1 .unit 0 := by
  decide +kernel

theorem separating_1_unit_1 :
    separatingPart certifiedCache 175 1 .unit 1 =
      separatingClaim 1 .unit 1 := by
  decide +kernel

theorem separating_1_hyperplane_0 :
    separatingPart certifiedCache 175 1 .hyperplane 0 =
      separatingClaim 1 .hyperplane 0 := by
  decide +kernel

theorem separating_1_hyperplane_1 :
    separatingPart certifiedCache 175 1 .hyperplane 1 =
      separatingClaim 1 .hyperplane 1 := by
  decide +kernel

theorem separating_1_exceptional_0 :
    separatingPart certifiedCache 175 1 (.exceptional 0) 0 =
      separatingClaim 1 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_1_exceptional_1 :
    separatingPart certifiedCache 175 1 (.exceptional 0) 1 =
      separatingClaim 1 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_1_point_0 :
    separatingPart certifiedCache 175 1 .point 0 =
      separatingClaim 1 .point 0 := by
  decide +kernel

theorem separating_1_point_1 :
    separatingPart certifiedCache 175 1 .point 1 =
      separatingClaim 1 .point 1 := by
  decide +kernel


end AxiomaticGW.BlowupF1FullRootReplay.Representative0175
