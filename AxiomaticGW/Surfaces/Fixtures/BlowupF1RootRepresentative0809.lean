/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootReplayFlatContext
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedComponentsRow0809

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay.Representative0809

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

/-- Exact certified selection; missing full keys retain the proved-equal fallback. -/
abbrev certifiedCache := AxiomaticGW.BlowupF1SelectedComponentsRow0809.cache

def claimed : ℚ := (-77 / 112320)

theorem coefficient_eq : L24CorrectionsReplay.fullClaim 809 = (-77 / 112320) := by
  decide +kernel

theorem maximum_genus_eq : (L24Gluing.term 809).expression.maxComponentGenus = 0 := by
  decide +kernel

theorem root_code_eq : rootCode (L24Gluing.term 809).expression = 2 := by
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
        ![0, 0],
        ![0, 0],
        ![0, 0],
        ![0, 0]
      ] : Fin 4 → Fin 2 → ℚ) i k
  | .exceptional _ =>
      (![
        ![0, 0],
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
  | .exceptional _ => (-77 / 112320)
  | .point => 0

theorem fundamental_eq :
    fundamentalPart certifiedCache 809 =
      fundamentalClaim := by
  decide +kernel

theorem separating_0_unit_0 :
    separatingPart certifiedCache 809 0 .unit 0 =
      separatingClaim 0 .unit 0 := by
  decide +kernel

theorem separating_0_unit_1 :
    separatingPart certifiedCache 809 0 .unit 1 =
      separatingClaim 0 .unit 1 := by
  decide +kernel

theorem separating_0_hyperplane_0 :
    separatingPart certifiedCache 809 0 .hyperplane 0 =
      separatingClaim 0 .hyperplane 0 := by
  decide +kernel

theorem separating_0_hyperplane_1 :
    separatingPart certifiedCache 809 0 .hyperplane 1 =
      separatingClaim 0 .hyperplane 1 := by
  decide +kernel

theorem separating_0_exceptional_0 :
    separatingPart certifiedCache 809 0 (.exceptional 0) 0 =
      separatingClaim 0 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_0_exceptional_1 :
    separatingPart certifiedCache 809 0 (.exceptional 0) 1 =
      separatingClaim 0 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_0_point_0 :
    separatingPart certifiedCache 809 0 .point 0 =
      separatingClaim 0 .point 0 := by
  decide +kernel

theorem separating_0_point_1 :
    separatingPart certifiedCache 809 0 .point 1 =
      separatingClaim 0 .point 1 := by
  decide +kernel

theorem separating_1_unit_0 :
    separatingPart certifiedCache 809 1 .unit 0 =
      separatingClaim 1 .unit 0 := by
  decide +kernel

theorem separating_1_unit_1 :
    separatingPart certifiedCache 809 1 .unit 1 =
      separatingClaim 1 .unit 1 := by
  decide +kernel

theorem separating_1_hyperplane_0 :
    separatingPart certifiedCache 809 1 .hyperplane 0 =
      separatingClaim 1 .hyperplane 0 := by
  decide +kernel

theorem separating_1_hyperplane_1 :
    separatingPart certifiedCache 809 1 .hyperplane 1 =
      separatingClaim 1 .hyperplane 1 := by
  decide +kernel

theorem separating_1_exceptional_0 :
    separatingPart certifiedCache 809 1 (.exceptional 0) 0 =
      separatingClaim 1 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_1_exceptional_1 :
    separatingPart certifiedCache 809 1 (.exceptional 0) 1 =
      separatingClaim 1 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_1_point_0 :
    separatingPart certifiedCache 809 1 .point 0 =
      separatingClaim 1 .point 0 := by
  decide +kernel

theorem separating_1_point_1 :
    separatingPart certifiedCache 809 1 .point 1 =
      separatingClaim 1 .point 1 := by
  decide +kernel

theorem separating_2_unit_0 :
    separatingPart certifiedCache 809 2 .unit 0 =
      separatingClaim 2 .unit 0 := by
  decide +kernel

theorem separating_2_unit_1 :
    separatingPart certifiedCache 809 2 .unit 1 =
      separatingClaim 2 .unit 1 := by
  decide +kernel

theorem separating_2_hyperplane_0 :
    separatingPart certifiedCache 809 2 .hyperplane 0 =
      separatingClaim 2 .hyperplane 0 := by
  decide +kernel

theorem separating_2_hyperplane_1 :
    separatingPart certifiedCache 809 2 .hyperplane 1 =
      separatingClaim 2 .hyperplane 1 := by
  decide +kernel

theorem separating_2_exceptional_0 :
    separatingPart certifiedCache 809 2 (.exceptional 0) 0 =
      separatingClaim 2 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_2_exceptional_1 :
    separatingPart certifiedCache 809 2 (.exceptional 0) 1 =
      separatingClaim 2 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_2_point_0 :
    separatingPart certifiedCache 809 2 .point 0 =
      separatingClaim 2 .point 0 := by
  decide +kernel

theorem separating_2_point_1 :
    separatingPart certifiedCache 809 2 .point 1 =
      separatingClaim 2 .point 1 := by
  decide +kernel

theorem separating_3_unit_0 :
    separatingPart certifiedCache 809 3 .unit 0 =
      separatingClaim 3 .unit 0 := by
  decide +kernel

theorem separating_3_unit_1 :
    separatingPart certifiedCache 809 3 .unit 1 =
      separatingClaim 3 .unit 1 := by
  decide +kernel

theorem separating_3_hyperplane_0 :
    separatingPart certifiedCache 809 3 .hyperplane 0 =
      separatingClaim 3 .hyperplane 0 := by
  decide +kernel

theorem separating_3_hyperplane_1 :
    separatingPart certifiedCache 809 3 .hyperplane 1 =
      separatingClaim 3 .hyperplane 1 := by
  decide +kernel

theorem separating_3_exceptional_0 :
    separatingPart certifiedCache 809 3 (.exceptional 0) 0 =
      separatingClaim 3 (.exceptional 0) 0 := by
  decide +kernel

theorem separating_3_exceptional_1 :
    separatingPart certifiedCache 809 3 (.exceptional 0) 1 =
      separatingClaim 3 (.exceptional 0) 1 := by
  decide +kernel

theorem separating_3_point_0 :
    separatingPart certifiedCache 809 3 .point 0 =
      separatingClaim 3 .point 0 := by
  decide +kernel

theorem separating_3_point_1 :
    separatingPart certifiedCache 809 3 .point 1 =
      separatingClaim 3 .point 1 := by
  decide +kernel

theorem nonseparating_unit :
    nonseparatingPart certifiedCache 809 .unit =
      nonseparatingClaim .unit := by
  decide +kernel

theorem nonseparating_hyperplane :
    nonseparatingPart certifiedCache 809 .hyperplane =
      nonseparatingClaim .hyperplane := by
  decide +kernel

theorem nonseparating_exceptional :
    nonseparatingPart certifiedCache 809 (.exceptional 0) =
      nonseparatingClaim (.exceptional 0) := by
  decide +kernel

theorem nonseparating_point :
    nonseparatingPart certifiedCache 809 .point =
      nonseparatingClaim .point := by
  decide +kernel

theorem low_genus : (L24Gluing.term 809).expression.maxComponentGenus < 2 := by
  rw [maximum_genus_eq]
  decide

theorem separating_eq (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) :
    separatingPart certifiedCache 809 i b k = separatingClaim i b k := by
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
    nonseparatingPart certifiedCache 809 b = nonseparatingClaim b := by
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

theorem original_eq_claimed : originalWeighted 809 = claimed := by
  rw [originalWeighted_eq_sum_claims certifiedCache 809 low_genus
    fundamentalClaim separatingClaim nonseparatingClaim
    fundamental_eq separating_eq nonseparating_eq]
  exact claimed_sum

end AxiomaticGW.BlowupF1FullRootReplay.Representative0809
