/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch00
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0128
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0129
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0130
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0131
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0132
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0134Replay
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0135
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch01
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0137
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0138
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0139
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0170
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0171
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0172
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0173
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0174Checked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0175Replay
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0176
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0177
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0178
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0179
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0180
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0181
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0182
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0183
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0184Checked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0185SecondChecked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0186
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0187
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0188
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0189
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0190
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0191
public import Mathlib.Tactic.FinCases

/-! # Checked interval of the original weighted F1 contraction

Each position uses its accepted original representative theorem, or the
original coefficient-ratio transfer followed by that representative theorem.
The component evaluator is never unfolded by this assembly.
-/

@[expose] public section
set_option autoImplicit false
namespace AxiomaticGW.BlowupF1WeightedAssembly
open scoped BigOperators

/-- Exact original positions 160 through 191. -/
theorem checkedBlock05 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 160 (Fin.castAdd 623 i)) =
      BlowupF1CandidateWeightedTable.block05 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 160 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 128 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0128.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted160_eq128, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 161 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 129 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0129.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted161_eq129, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 162 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 130 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0130.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted162_eq130, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 163 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 131 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0131.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted163_eq131, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 164 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 132 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0132.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted164_eq132, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 165 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 134 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0134.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted165_eq134, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 166 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 135 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0135.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch00.weighted166_eq135, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 167 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 137 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0137.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted167_eq137, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 168 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 138 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0138.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted168_eq138, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 169 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 139 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0139.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted169_eq139, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 170 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0170.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 171 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0171.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 172 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0172.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 173 = (-1481 / 151632 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0173.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 174 = (-161 / 19440 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0174.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 175 = (1525 / 75816 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0175.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 176 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0176.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 177 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0177.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 178 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0178.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 179 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0179.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 180 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0180.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 181 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0181.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 182 = (4259 / 1010880 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0182.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 183 = (1 / 4320 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0183.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 184 = (161 / 77760 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0184.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 185 = (-745 / 101088 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0185.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 186 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0186.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 187 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0187.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 188 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0188.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 189 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0189.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 190 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0190.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 191 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0191.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock05_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 160 (Fin.castAdd 623 i))) = (17 / 14040 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block05 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock05 i)
    _ = _ := BlowupF1CandidateWeightedTable.block05_sum

end AxiomaticGW.BlowupF1WeightedAssembly
