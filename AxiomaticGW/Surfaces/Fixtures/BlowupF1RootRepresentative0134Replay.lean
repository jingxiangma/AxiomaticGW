/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0134FirstSplits
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0134LastSplits

@[expose] public section
set_option maxRecDepth 65536
set_option Elab.async false
set_option maxHeartbeats 0

namespace AxiomaticGW.BlowupF1FullRootReplay.Representative0134

open AxiomaticGW BlowupF1RootAssembly
open scoped BigOperators

theorem low_genus : (L24Gluing.term 134).expression.maxComponentGenus < 2 := by
  rw [maximum_genus_eq]
  decide

theorem separating_eq (i : Fin 4) (b : SurfaceBasisLabel X) (k : Fin 2) :
    separatingPart certifiedCache 134 i b k = separatingClaim i b k := by
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
    nonseparatingPart certifiedCache 134 b = nonseparatingClaim b := by
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

theorem original_eq_claimed : originalWeighted 134 = claimed := by
  rw [originalWeighted_eq_sum_claims certifiedCache 134 low_genus
    fundamentalClaim separatingClaim nonseparatingClaim
    fundamental_eq separating_eq nonseparating_eq]
  exact claimed_sum

end AxiomaticGW.BlowupF1FullRootReplay.Representative0134
