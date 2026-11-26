/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch03
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.GuardBatch00
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.GuardBatch01
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootIndex0122
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0123Checked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0124SecondChecked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0125
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0126
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0127
public import Mathlib.Tactic.FinCases

/-! # Original weighted rows 96 through 127

The adapter uses the previously proved zero and representative rows.
It retains the original indices, including both kinds of guarded zero and
positive and negative weighted values. It does not evaluate a component cache
or assert the other blocks of the full contraction.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.BlowupF1WeightedAssembly
open scoped BigOperators

/-- Every original row in the fourth interval equals its frozen table entry. -/
theorem checkedBlock03 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 96 (Fin.castAdd 687 i)) =
      BlowupF1CandidateWeightedTable.block03 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 96 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted96
  · change BlowupF1RootAssembly.originalWeighted 97 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted97
  · change BlowupF1RootAssembly.originalWeighted 98 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted98
  · change BlowupF1RootAssembly.originalWeighted 99 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted99
  · change BlowupF1RootAssembly.originalWeighted 100 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted100
  · change BlowupF1RootAssembly.originalWeighted 101 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted101
  · change BlowupF1RootAssembly.originalWeighted 102 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted102
  · change BlowupF1RootAssembly.originalWeighted 103 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted103
  · change BlowupF1RootAssembly.originalWeighted 104 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted104
  · change BlowupF1RootAssembly.originalWeighted 105 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted105
  · change BlowupF1RootAssembly.originalWeighted 106 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted106
  · change BlowupF1RootAssembly.originalWeighted 107 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted107
  · change BlowupF1RootAssembly.originalWeighted 108 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted108
  · change BlowupF1RootAssembly.originalWeighted 109 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted109
  · change BlowupF1RootAssembly.originalWeighted 110 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted110
  · change BlowupF1RootAssembly.originalWeighted 111 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted111
  · change BlowupF1RootAssembly.originalWeighted 112 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted112
  · change BlowupF1RootAssembly.originalWeighted 113 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted113
  · change BlowupF1RootAssembly.originalWeighted 114 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted114
  · change BlowupF1RootAssembly.originalWeighted 115 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted115
  · change BlowupF1RootAssembly.originalWeighted 116 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted116
  · change BlowupF1RootAssembly.originalWeighted 117 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted117
  · change BlowupF1RootAssembly.originalWeighted 118 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted118
  · change BlowupF1RootAssembly.originalWeighted 119 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch01.weighted119
  · change BlowupF1RootAssembly.originalWeighted 120 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch01.weighted120
  · change BlowupF1RootAssembly.originalWeighted 121 = (1 / 2160 : ℚ)
    exact AxiomaticGW.BlowupF1RootAssembly.originalWeighted121
  · change BlowupF1RootAssembly.originalWeighted 122 = (4259 / 505440 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Index0122.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 123 = (161 / 38880 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0123.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 124 = (-745 / 50544 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0124.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 125 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0125.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 126 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0126.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 127 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0127.original_eq_claimed

/-- Sum this actual interval using its checked table, without unfolding the evaluator. -/
theorem originalBlock03_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 96 (Fin.castAdd 687 i))) = (-1 / 585 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block03 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock03 i)
    _ = _ := BlowupF1CandidateWeightedTable.block03_sum

end AxiomaticGW.BlowupF1WeightedAssembly
