module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable

/-! Tests of the frozen arithmetic table; no project evaluator is imported. -/

@[expose] public section

namespace AxiomaticGWTest.BlowupF1CandidateWeightedTable

open AxiomaticGW.BlowupF1CandidateWeightedTable
open scoped BigOperators

theorem original_zero_position : claimed 0 = 0 := by
  decide +kernel

theorem original121_position : claimed 121 = (1 / 2160 : ℚ) := by
  decide +kernel

theorem last_block_start : claimed 800 = 0 := by
  decide +kernel

theorem original_final_position : claimed 814 = (31 / 33696 : ℚ) := by
  decide +kernel

theorem candidate_total : (∑ j : Fin 815, claimed j) = (1 / 288 : ℚ) :=
  claimed_sum

end AxiomaticGWTest.BlowupF1CandidateWeightedTable
