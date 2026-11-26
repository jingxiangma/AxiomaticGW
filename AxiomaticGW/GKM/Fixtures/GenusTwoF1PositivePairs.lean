/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoPositivePairReplay
public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.OneBlowup

/-! # The nine positive-pair ordinary comparisons on the exceptional of the first blowup -/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoPositivePairs
open SurfaceGenusTwoBlowupDescendants

namespace OneBlowup

/-- Ordinary GKM specialization agrees with the full ordered reconstruction throughout the grid. -/
theorem all_accepted (j k : Fin 3) :
    queryValue? 0 (requests j k) = some (values j k) := by
  cases j using Fin.cases with
  | zero =>
    fin_cases k
    · exact GenusTwoSecondUnitPairs.OneBlowup.accepted 0
    · exact GenusTwoSecondUnitPairs.OneBlowup.accepted 1
    · exact GenusTwoSecondUnitPairs.OneBlowup.accepted 2
  | succ j =>
    cases k using Fin.cases with
    | zero =>
      fin_cases j
      · exact GenusTwoSecondUnitPairs.OneBlowup.accepted 3
      · exact GenusTwoSecondUnitPairs.OneBlowup.accepted 4
    | succ k => exact divisors_accepted j k

end OneBlowup

end AxiomaticGW.GKM.GenusTwoPositivePairs
