/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0128
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0129
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0130
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0131
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0132
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0133Checked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0134Replay
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0135
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0136
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0137
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0138
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0139
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch00
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootIndex0122
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0124SecondChecked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0126
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0127
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch01
public import Mathlib.Tactic.FinCases

/-! # Checked interval of the original weighted F1 contraction

Every position reuses its accepted zero or representative theorem, or the
original structural coefficient-ratio transfer followed by its representative.
The component evaluator is never unfolded by this assembly.
-/

@[expose] public section
set_option autoImplicit false
namespace AxiomaticGW.BlowupF1WeightedAssembly
open scoped BigOperators

/-- Exact original positions 128 through 159. -/
theorem checkedBlock04 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 128 (Fin.castAdd 655 i)) =
      BlowupF1CandidateWeightedTable.block04 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 128 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0128.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 129 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0129.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 130 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0130.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 131 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0131.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 132 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0132.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 133 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0133.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 134 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0134.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 135 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0135.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 136 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0136.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 137 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0137.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 138 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0138.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 139 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0139.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 140 = (3527 / 758160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 121 = (1 / 2160 : ℚ) :=
      AxiomaticGW.BlowupF1RootAssembly.originalWeighted121
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted140_eq121, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 141 = (3527 / 758160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 122 = (4259 / 505440 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Index0122.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted141_eq122, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 142 = (-745 / 75816 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 124 = (-745 / 50544 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0124.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted142_eq124, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 143 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 126 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0126.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted143_eq126, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 144 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 127 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0127.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted144_eq127, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 145 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 128 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0128.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted145_eq128, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 146 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 129 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0129.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted146_eq129, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 147 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 130 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0130.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted147_eq130, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 148 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 131 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0131.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted148_eq131, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 149 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 132 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0132.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted149_eq132, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 150 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 134 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0134.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted150_eq134, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 151 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 135 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0135.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted151_eq135, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 152 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 137 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0137.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted152_eq137, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 153 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 138 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0138.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted153_eq138, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 154 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 139 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0139.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted154_eq139, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 155 = (3527 / 758160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 121 = (1 / 2160 : ℚ) :=
      AxiomaticGW.BlowupF1RootAssembly.originalWeighted121
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted155_eq121, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 156 = (3527 / 758160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 122 = (4259 / 505440 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Index0122.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted156_eq122, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 157 = (-745 / 75816 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 124 = (-745 / 50544 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0124.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted157_eq124, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 158 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 126 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0126.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted158_eq126, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 159 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 127 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0127.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted159_eq127, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock04_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 128 (Fin.castAdd 655 i))) = (-11 / 10530 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block04 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock04 i)
    _ = _ := BlowupF1CandidateWeightedTable.block04_sum

end AxiomaticGW.BlowupF1WeightedAssembly
