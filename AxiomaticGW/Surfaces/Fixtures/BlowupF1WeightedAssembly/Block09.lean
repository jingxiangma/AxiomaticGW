/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch03
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0279
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0280
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0281
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0291
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0292
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0293
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0294
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0295
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0296
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0297
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0298
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0299
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch04
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0304
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0305
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0306
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0307
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0319
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

/-- Exact original positions 288 through 319. -/
theorem checkedBlock09 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 288 (Fin.castAdd 495 i)) =
      BlowupF1CandidateWeightedTable.block09 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 288 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 279 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0279.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted288_eq279, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 289 = (1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 280 = (1 / 864 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0280.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted289_eq280, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 290 = (1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 281 = (1 / 480 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0281.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted290_eq281, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 291 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0291.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 292 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0292.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 293 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0293.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 294 = (1 / 1440 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0294.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 295 = (-1 / 180 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0295.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 296 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0296.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 297 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0297.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 298 = (1 / 240 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0298.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 299 = (1 / 432 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0299.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 300 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 296 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0296.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted300_eq296, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 301 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 297 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0297.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted301_eq297, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 302 = (1 / 240 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 298 = (1 / 240 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0298.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted302_eq298, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 303 = (1 / 432 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 299 = (1 / 432 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0299.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted303_eq299, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 304 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0304.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 305 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0305.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 306 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0306.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 307 = (1 / 240 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0307.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 308 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 296 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0296.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch03.weighted308_eq296, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 309 = (1 / 1080 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 298 = (1 / 240 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0298.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted309_eq298, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 310 = (1 / 1080 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 299 = (1 / 432 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0299.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted310_eq299, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 311 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 304 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0304.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted311_eq304, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 312 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 305 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0305.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted312_eq305, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 313 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 306 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0306.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted313_eq306, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 314 = (1 / 720 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 307 = (1 / 240 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0307.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted314_eq307, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 315 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 304 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0304.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted315_eq304, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 316 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 305 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0305.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted316_eq305, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 317 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 306 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0306.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted317_eq306, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 318 = (1 / 720 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 307 = (1 / 240 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0307.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted318_eq307, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 319 = (1 / 17280 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0319.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock09_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 288 (Fin.castAdd 495 i))) = (103 / 5760 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block09 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock09 i)
    _ = _ := BlowupF1CandidateWeightedTable.block09_sum

end AxiomaticGW.BlowupF1WeightedAssembly
