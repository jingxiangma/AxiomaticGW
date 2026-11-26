/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0134Data

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay.Representative0134

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

theorem separating_2_unit_0 :
    separatingPart certifiedCache 134 2 .unit 0 =
      separatingClaim 2 .unit 0 := by
  decide +kernel

theorem separating_2_unit_1 :
    separatingPart certifiedCache 134 2 .unit 1 =
      separatingClaim 2 .unit 1 := by
  decide +kernel

theorem separating_2_hyperplane_0 :
    separatingPart certifiedCache 134 2 .hyperplane 0 =
      separatingClaim 2 .hyperplane 0 := by
  decide +kernel

theorem separating_2_hyperplane_1 :
    separatingPart certifiedCache 134 2 .hyperplane 1 =
      separatingClaim 2 .hyperplane 1 := by
  decide +kernel

theorem separating_2_exceptional_0 :
    separatingPart certifiedCache 134 2 (.exceptional 0) 0 =
      separatingClaim 2 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_2_exceptional_1 :
    separatingPart certifiedCache 134 2 (.exceptional 0) 1 =
      separatingClaim 2 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_2_point_0 :
    separatingPart certifiedCache 134 2 .point 0 =
      separatingClaim 2 .point 0 := by
  decide +kernel

theorem separating_2_point_1 :
    separatingPart certifiedCache 134 2 .point 1 =
      separatingClaim 2 .point 1 := by
  decide +kernel

theorem separating_3_unit_0 :
    separatingPart certifiedCache 134 3 .unit 0 =
      separatingClaim 3 .unit 0 := by
  decide +kernel

theorem separating_3_unit_1 :
    separatingPart certifiedCache 134 3 .unit 1 =
      separatingClaim 3 .unit 1 := by
  decide +kernel

theorem separating_3_hyperplane_0 :
    separatingPart certifiedCache 134 3 .hyperplane 0 =
      separatingClaim 3 .hyperplane 0 := by
  decide +kernel

theorem separating_3_hyperplane_1 :
    separatingPart certifiedCache 134 3 .hyperplane 1 =
      separatingClaim 3 .hyperplane 1 := by
  decide +kernel

theorem separating_3_exceptional_0 :
    separatingPart certifiedCache 134 3 (.exceptional 0) 0 =
      separatingClaim 3 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_3_exceptional_1 :
    separatingPart certifiedCache 134 3 (.exceptional 0) 1 =
      separatingClaim 3 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_3_point_0 :
    separatingPart certifiedCache 134 3 .point 0 =
      separatingClaim 3 .point 0 := by
  decide +kernel

theorem separating_3_point_1 :
    separatingPart certifiedCache 134 3 .point 1 =
      separatingClaim 3 .point 1 := by
  decide +kernel

theorem nonseparating_unit :
    nonseparatingPart certifiedCache 134 .unit =
      nonseparatingClaim .unit := by
  decide +kernel

theorem nonseparating_hyperplane :
    nonseparatingPart certifiedCache 134 .hyperplane =
      nonseparatingClaim .hyperplane := by
  decide +kernel

theorem nonseparating_exceptional :
    nonseparatingPart certifiedCache 134 (.exceptional 0) =
      nonseparatingClaim (.exceptional 0) := by
  decide +kernel

theorem nonseparating_point :
    nonseparatingPart certifiedCache 134 .point =
      nonseparatingClaim .point := by
  decide +kernel


end AxiomaticGW.BlowupF1FullRootReplay.Representative0134
