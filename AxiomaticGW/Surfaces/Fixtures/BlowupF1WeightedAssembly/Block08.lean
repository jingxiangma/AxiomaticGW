/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch03
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0229
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0230
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0231
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0232
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch02
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0220Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0221Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0222Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0223Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0224Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0225Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0226
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0228
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0272Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0273Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0274Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0275Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0276
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0278
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0279
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0280
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0281
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0282
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0284
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

/-- Exact original positions 256 through 287. -/
theorem checkedBlock08 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 256 (Fin.castAdd 527 i)) =
      BlowupF1CandidateWeightedTable.block08 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 256 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 229 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0229.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted256_eq229, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 257 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 230 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0230.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted257_eq230, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 258 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 231 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0231.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted258_eq231, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 259 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 232 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0232.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted259_eq232, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 260 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 220 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0220.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted260_eq220, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 261 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 221 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0221.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted261_eq221, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 262 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 222 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0222.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted262_eq222, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 263 = (-1481 / 303264 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 223 = (-1285 / 134784 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0223.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted263_eq223, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 264 = (-161 / 38880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 224 = (-161 / 17280 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0224.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch02.weighted264_eq224, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 265 = (1525 / 151632 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 225 = (745 / 33696 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0225.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted265_eq225, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 266 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 226 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0226.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted266_eq226, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 267 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 228 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0228.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted267_eq228, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 268 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 229 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0229.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted268_eq229, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 269 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 230 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0230.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted269_eq230, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 270 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 231 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0231.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted270_eq231, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 271 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 232 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0232.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted271_eq232, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 272 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0272.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 273 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0273.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 274 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0274.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 275 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0275.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 276 = (-1 / 360 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0276.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 277 = (-1 / 360 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 276 = (-1 / 360 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0276.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted277_eq276, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 278 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0278.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 279 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0279.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 280 = (1 / 864 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0280.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 281 = (1 / 480 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0281.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 282 = (-1 / 2160 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0282.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 283 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 276 = (-1 / 360 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0276.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted283_eq276, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 284 = (-1 / 2160 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0284.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 285 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 279 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0279.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted285_eq279, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 286 = (1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 280 = (1 / 864 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0280.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted286_eq280, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 287 = (1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 281 = (1 / 480 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0281.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted287_eq281, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock08_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 256 (Fin.castAdd 527 i))) = (-49 / 28080 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block08 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock08 i)
    _ = _ := BlowupF1CandidateWeightedTable.block08_sum

end AxiomaticGW.BlowupF1WeightedAssembly
