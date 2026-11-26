/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch08
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0457
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0459
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0470
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0471
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0472
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0489Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch09
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0492Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0493Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0495Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0499
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0500
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0501
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0502
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0509
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0510
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0511
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

/-- Exact original positions 480 through 511. -/
theorem checkedBlock15 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 480 (Fin.castAdd 303 i)) =
      BlowupF1CandidateWeightedTable.block15 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 480 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 457 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0457.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted480_eq457, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 481 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 457 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0457.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted481_eq457, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 482 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 459 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0459.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted482_eq459, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 483 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 470 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0470.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted483_eq470, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 484 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 471 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0471.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted484_eq471, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 485 = (7 / 14976 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 472 = (73 / 74880 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0472.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted485_eq472, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 486 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 470 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0470.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted486_eq470, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 487 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 471 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0471.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted487_eq471, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 488 = (7 / 14976 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 472 = (73 / 74880 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0472.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted488_eq472, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 489 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0489.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 490 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 489 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0489.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted490_eq489, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 491 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 489 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0489.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted491_eq489, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 492 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0492.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 493 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0493.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 494 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 493 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0493.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted494_eq493, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 495 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0495.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 496 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 493 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0493.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted496_eq493, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 497 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 495 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0495.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted497_eq495, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 498 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 495 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0495.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted498_eq495, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 499 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0499.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 500 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0500.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 501 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0501.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 502 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0502.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 503 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 499 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0499.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted503_eq499, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 504 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 500 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0500.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted504_eq500, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 505 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 501 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0501.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted505_eq501, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 506 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 499 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0499.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted506_eq499, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 507 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 500 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0500.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted507_eq500, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 508 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 501 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0501.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted508_eq501, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 509 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0509.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 510 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0510.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 511 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0511.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock15_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 480 (Fin.castAdd 303 i))) = (7 / 7488 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block15 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock15 i)
    _ = _ := BlowupF1CandidateWeightedTable.block15_sum

end AxiomaticGW.BlowupF1WeightedAssembly
