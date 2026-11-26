/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0224Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0225Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0226
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0227
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0228
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0229
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0230
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0231
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0232
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch01
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0182
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0183
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0185SecondChecked
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0187
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0188
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0189
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0190
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0191
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0192
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch02
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0193Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0195Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0196
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0198
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0199
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0200
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0220Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0221Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0222Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0223Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch03
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

/-- Exact original positions 224 through 255. -/
theorem checkedBlock07 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 224 (Fin.castAdd 559 i)) =
      BlowupF1CandidateWeightedTable.block07 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 224 = (-161 / 17280 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0224.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 225 = (745 / 33696 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0225.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 226 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0226.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 227 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0227.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 228 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0228.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 229 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0229.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 230 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0230.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 231 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0231.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 232 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0232.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 233 = (3527 / 1516320 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 182 = (4259 / 1010880 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0182.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted233_eq182, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 234 = (3527 / 1516320 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 183 = (1 / 4320 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0183.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted234_eq183, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 235 = (-745 / 151632 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 185 = (-745 / 101088 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0185.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted235_eq185, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 236 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 187 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0187.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted236_eq187, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 237 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 188 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0188.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted237_eq188, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 238 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 189 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0189.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted238_eq189, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 239 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 190 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0190.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted239_eq190, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 240 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 191 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0191.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted240_eq191, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 241 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 192 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0192.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch01.weighted241_eq192, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 242 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 193 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0193.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted242_eq193, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 243 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 195 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0195.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted243_eq195, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 244 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 196 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0196.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted244_eq196, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 245 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 198 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0198.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted245_eq198, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 246 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 199 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0199.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted246_eq199, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 247 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 200 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0200.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted247_eq200, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 248 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 220 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0220.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted248_eq220, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 249 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 221 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0221.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted249_eq221, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 250 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 222 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0222.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted250_eq222, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 251 = (-1481 / 303264 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 223 = (-1285 / 134784 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0223.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted251_eq223, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 252 = (-161 / 38880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 224 = (-161 / 17280 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0224.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted252_eq224, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 253 = (1525 / 151632 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 225 = (745 / 33696 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0225.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted253_eq225, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 254 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 226 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0226.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted254_eq226, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 255 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 228 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0228.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted255_eq228, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock07_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 224 (Fin.castAdd 559 i))) = (3047 / 224640 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block07 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock07 i)
    _ = _ := BlowupF1CandidateWeightedTable.block07_sum

end AxiomaticGW.BlowupF1WeightedAssembly
