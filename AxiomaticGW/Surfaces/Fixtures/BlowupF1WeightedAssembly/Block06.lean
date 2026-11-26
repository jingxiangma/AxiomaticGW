/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0192
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0193Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0194Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0195Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0196
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0197
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0198
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0199
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0200
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch01
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
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch02
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0220Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0221Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0222Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0223Ordered
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

/-- Exact original positions 192 through 223. -/
theorem checkedBlock06 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 192 (Fin.castAdd 591 i)) =
      BlowupF1CandidateWeightedTable.block06 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 192 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0192.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 193 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0193.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 194 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0194.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 195 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0195.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 196 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0196.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 197 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0197.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 198 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0198.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 199 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0199.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 200 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0200.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 201 = (4259 / 1010880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 182 = (4259 / 1010880 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0182.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted201_eq182, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 202 = (1 / 4320 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 183 = (1 / 4320 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0183.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted202_eq183, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 203 = (161 / 77760 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 184 = (161 / 77760 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0184.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted203_eq184, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 204 = (-745 / 101088 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 185 = (-745 / 101088 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0185.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted204_eq185, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 205 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 186 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0186.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted205_eq186, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 206 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 187 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0187.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted206_eq187, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 207 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 188 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0188.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted207_eq188, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 208 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 189 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0189.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted208_eq189, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 209 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 190 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0190.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted209_eq190, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 210 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 191 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0191.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted210_eq191, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 211 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 192 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0192.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted211_eq192, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 212 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 193 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0193.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted212_eq193, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 213 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 194 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0194.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted213_eq194, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 214 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 195 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0195.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted214_eq195, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 215 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 196 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0196.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted215_eq196, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 216 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 197 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0197.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted216_eq197, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 217 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 198 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0198.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted217_eq198, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 218 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 199 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0199.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted218_eq199, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 219 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 200 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0200.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted219_eq200, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 220 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0220.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 221 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0221.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 222 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0222.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 223 = (-1285 / 134784 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0223.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock06_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 192 (Fin.castAdd 591 i))) = (-7001 / 673920 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block06 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock06 i)
    _ = _ := BlowupF1CandidateWeightedTable.block06_sum

end AxiomaticGW.BlowupF1WeightedAssembly
