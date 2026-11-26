/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootReplayFlatContext
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedComponentsRow0124
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Root124DimensionZero
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1Root124PointDimensionZero

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay.Representative0124

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

/-- Exact certified selection; missing full keys retain the proved-equal fallback. -/
abbrev certifiedCache := AxiomaticGW.BlowupF1SelectedComponentsRow0124.cache

def claimed : ℚ := (-745 / 50544)

theorem coefficient_eq : L24CorrectionsReplay.fullClaim 124 = (-745 / 351) := by
  decide +kernel

theorem maximum_genus_eq : (L24Gluing.term 124).expression.maxComponentGenus = 1 := by
  decide +kernel

theorem root_code_eq : rootCode (L24Gluing.term 124).expression = 1 := by
  decide +kernel

def fundamentalClaim : ℚ := 0

def separatingClaim (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) : ℚ :=
  match b with
  | .unit =>
      (![
        ![0, 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .hyperplane =>
      (![
        ![(-745 / 33696), 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .exceptional _ =>
      (![
        ![(745 / 101088), 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .point =>
      (![
        ![0, 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k

def nonseparatingClaim (b : SurfaceBasisLabel X) : ℚ :=
  match b with
  | .unit => 0
  | .hyperplane => 0
  | .exceptional _ => 0
  | .point => 0

theorem fundamental_eq :
    fundamentalPart certifiedCache 124 =
      fundamentalClaim := by
  decide +kernel

theorem separating_0_unit_0 :
    separatingPart certifiedCache 124 0 .unit 0 =
      separatingClaim 0 .unit 0 := by
  exact BlowupF1Root124DimensionZero.separating124_split0_unit_point0 certifiedCache

theorem separating_0_unit_1 :
    separatingPart certifiedCache 124 0 .unit 1 =
      separatingClaim 0 .unit 1 := by
  decide +kernel

theorem separating_0_hyperplane_0 :
    separatingPart certifiedCache 124 0 .hyperplane 0 =
      separatingClaim 0 .hyperplane 0 := by
  decide +kernel

theorem separating_0_hyperplane_1 :
    separatingPart certifiedCache 124 0 .hyperplane 1 =
      separatingClaim 0 .hyperplane 1 := by
  decide +kernel

theorem separating_0_exceptional_0 :
    separatingPart certifiedCache 124 0 (.exceptional 0) 0 =
      separatingClaim 0 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_0_exceptional_1 :
    separatingPart certifiedCache 124 0 (.exceptional 0) 1 =
      separatingClaim 0 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_0_point_0 :
    separatingPart certifiedCache 124 0 .point 0 =
      separatingClaim 0 .point 0 := by
  exact BlowupF1Root124PointDimensionZero.separating124_split0_point_point0 certifiedCache

theorem separating_0_point_1 :
    separatingPart certifiedCache 124 0 .point 1 =
      separatingClaim 0 .point 1 := by
  decide +kernel

theorem separating_1_unit_0 :
    separatingPart certifiedCache 124 1 .unit 0 =
      separatingClaim 1 .unit 0 := by
  decide +kernel

theorem separating_1_unit_1 :
    separatingPart certifiedCache 124 1 .unit 1 =
      separatingClaim 1 .unit 1 := by
  decide +kernel

theorem separating_1_hyperplane_0 :
    separatingPart certifiedCache 124 1 .hyperplane 0 =
      separatingClaim 1 .hyperplane 0 := by
  decide +kernel

theorem separating_1_hyperplane_1 :
    separatingPart certifiedCache 124 1 .hyperplane 1 =
      separatingClaim 1 .hyperplane 1 := by
  decide +kernel

theorem separating_1_exceptional_0 :
    separatingPart certifiedCache 124 1 (.exceptional 0) 0 =
      separatingClaim 1 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_1_exceptional_1 :
    separatingPart certifiedCache 124 1 (.exceptional 0) 1 =
      separatingClaim 1 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_1_point_0 :
    separatingPart certifiedCache 124 1 .point 0 =
      separatingClaim 1 .point 0 := by
  decide +kernel

theorem separating_1_point_1 :
    separatingPart certifiedCache 124 1 .point 1 =
      separatingClaim 1 .point 1 := by
  decide +kernel

theorem separating_2_unit_0 :
    separatingPart certifiedCache 124 2 .unit 0 =
      separatingClaim 2 .unit 0 := by
  decide +kernel

theorem separating_2_unit_1 :
    separatingPart certifiedCache 124 2 .unit 1 =
      separatingClaim 2 .unit 1 := by
  decide +kernel

theorem separating_2_hyperplane_0 :
    separatingPart certifiedCache 124 2 .hyperplane 0 =
      separatingClaim 2 .hyperplane 0 := by
  decide +kernel

theorem separating_2_hyperplane_1 :
    separatingPart certifiedCache 124 2 .hyperplane 1 =
      separatingClaim 2 .hyperplane 1 := by
  decide +kernel

theorem separating_2_exceptional_0 :
    separatingPart certifiedCache 124 2 (.exceptional 0) 0 =
      separatingClaim 2 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_2_exceptional_1 :
    separatingPart certifiedCache 124 2 (.exceptional 0) 1 =
      separatingClaim 2 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_2_point_0 :
    separatingPart certifiedCache 124 2 .point 0 =
      separatingClaim 2 .point 0 := by
  decide +kernel

theorem separating_2_point_1 :
    separatingPart certifiedCache 124 2 .point 1 =
      separatingClaim 2 .point 1 := by
  decide +kernel

theorem separating_3_unit_0 :
    separatingPart certifiedCache 124 3 .unit 0 =
      separatingClaim 3 .unit 0 := by
  decide +kernel

theorem separating_3_unit_1 :
    separatingPart certifiedCache 124 3 .unit 1 =
      separatingClaim 3 .unit 1 := by
  decide +kernel

theorem separating_3_hyperplane_0 :
    separatingPart certifiedCache 124 3 .hyperplane 0 =
      separatingClaim 3 .hyperplane 0 := by
  decide +kernel

theorem separating_3_hyperplane_1 :
    separatingPart certifiedCache 124 3 .hyperplane 1 =
      separatingClaim 3 .hyperplane 1 := by
  decide +kernel

theorem separating_3_exceptional_0 :
    separatingPart certifiedCache 124 3 (.exceptional 0) 0 =
      separatingClaim 3 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_3_exceptional_1 :
    separatingPart certifiedCache 124 3 (.exceptional 0) 1 =
      separatingClaim 3 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_3_point_0 :
    separatingPart certifiedCache 124 3 .point 0 =
      separatingClaim 3 .point 0 := by
  decide +kernel

theorem separating_3_point_1 :
    separatingPart certifiedCache 124 3 .point 1 =
      separatingClaim 3 .point 1 := by
  decide +kernel

theorem nonseparating_unit :
    nonseparatingPart certifiedCache 124 .unit =
      nonseparatingClaim .unit := by
  decide +kernel

theorem nonseparating_hyperplane :
    nonseparatingPart certifiedCache 124 .hyperplane =
      nonseparatingClaim .hyperplane := by
  decide +kernel

theorem nonseparating_exceptional :
    nonseparatingPart certifiedCache 124 (.exceptional 0) =
      nonseparatingClaim (.exceptional 0) := by
  decide +kernel

theorem nonseparating_point :
    nonseparatingPart certifiedCache 124 .point =
      nonseparatingClaim .point := by
  decide +kernel

theorem low_genus : (L24Gluing.term 124).expression.maxComponentGenus < 2 := by
  rw [maximum_genus_eq]
  decide

theorem separating_eq (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) :
    separatingPart certifiedCache 124 i b k = separatingClaim i b k := by
  fin_cases i
  · cases b with
    | unit =>
      fin_cases k
      · exact separating_0_unit_0
      · exact separating_0_unit_1
    | hyperplane =>
      fin_cases k
      · exact separating_0_hyperplane_0
      · exact separating_0_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact separating_0_exceptional_0
      · exact separating_0_exceptional_1
    | point =>
      fin_cases k
      · exact separating_0_point_0
      · exact separating_0_point_1
  · cases b with
    | unit =>
      fin_cases k
      · exact separating_1_unit_0
      · exact separating_1_unit_1
    | hyperplane =>
      fin_cases k
      · exact separating_1_hyperplane_0
      · exact separating_1_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact separating_1_exceptional_0
      · exact separating_1_exceptional_1
    | point =>
      fin_cases k
      · exact separating_1_point_0
      · exact separating_1_point_1
  · cases b with
    | unit =>
      fin_cases k
      · exact separating_2_unit_0
      · exact separating_2_unit_1
    | hyperplane =>
      fin_cases k
      · exact separating_2_hyperplane_0
      · exact separating_2_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact separating_2_exceptional_0
      · exact separating_2_exceptional_1
    | point =>
      fin_cases k
      · exact separating_2_point_0
      · exact separating_2_point_1
  · cases b with
    | unit =>
      fin_cases k
      · exact separating_3_unit_0
      · exact separating_3_unit_1
    | hyperplane =>
      fin_cases k
      · exact separating_3_hyperplane_0
      · exact separating_3_hyperplane_1
    | exceptional e =>
      fin_cases e
      fin_cases k
      · exact separating_3_exceptional_0
      · exact separating_3_exceptional_1
    | point =>
      fin_cases k
      · exact separating_3_point_0
      · exact separating_3_point_1

theorem nonseparating_eq (b : SurfaceBasisLabel X) :
    nonseparatingPart certifiedCache 124 b = nonseparatingClaim b := by
  cases b with
  | unit => exact nonseparating_unit
  | hyperplane => exact nonseparating_hyperplane
  | exceptional e =>
    fin_cases e
    exact nonseparating_exceptional
  | point => exact nonseparating_point

theorem claimed_sum : fundamentalClaim +
    (∑ i : Fin 4, ∑ b : SurfaceBasisLabel X, ∑ k : Fin 2, separatingClaim i b k) +
    (∑ b : SurfaceBasisLabel X, nonseparatingClaim b) = claimed := by
  decide +kernel

theorem original_eq_claimed : originalWeighted 124 = claimed := by
  rw [originalWeighted_eq_sum_claims certifiedCache 124 low_genus
    fundamentalClaim separatingClaim nonseparatingClaim
    fundamental_eq separating_eq nonseparating_eq]
  exact claimed_sum

end AxiomaticGW.BlowupF1FullRootReplay.Representative0124
