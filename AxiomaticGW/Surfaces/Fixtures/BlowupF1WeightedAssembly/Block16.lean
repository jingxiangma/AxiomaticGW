/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0512
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0513
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0514
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0515
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0516
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0517
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0518
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch09
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0523
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0524
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0525
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0526
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0527
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0528
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch10
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

/-- Exact original positions 512 through 543. -/
theorem checkedBlock16 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 512 (Fin.castAdd 271 i)) =
      BlowupF1CandidateWeightedTable.block16 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 512 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0512.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 513 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0513.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 514 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0514.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 515 = (-539 / 67392 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0515.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 516 = (101 / 18720 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0516.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 517 = (1 / 4320 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0517.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 518 = (67 / 25920 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0518.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 519 = (-539 / 67392 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 515 = (-539 / 67392 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0515.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted519_eq515, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 520 = (101 / 18720 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 516 = (101 / 18720 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0516.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted520_eq516, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 521 = (1 / 4320 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 517 = (1 / 4320 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0517.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted521_eq517, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 522 = (67 / 25920 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 518 = (67 / 25920 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0518.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted522_eq518, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 523 = (539 / 22464 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0523.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 524 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0524.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 525 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0525.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 526 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0526.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 527 = (-553 / 44928 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0527.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 528 = (-67 / 5760 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0528.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 529 = (-539 / 101088 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 515 = (-539 / 67392 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0515.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted529_eq515, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 530 = (2923 / 1010880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 516 = (101 / 18720 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0516.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted530_eq516, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 531 = (2923 / 1010880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 517 = (1 / 4320 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0517.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted531_eq517, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 532 = (1085 / 101088 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 523 = (539 / 22464 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0523.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted532_eq523, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 533 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 524 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0524.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted533_eq524, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 534 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 525 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0525.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted534_eq525, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 535 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 526 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0526.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted535_eq526, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 536 = (-19 / 3159 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 527 = (-553 / 44928 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0527.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted536_eq527, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 537 = (-67 / 12960 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 528 = (-67 / 5760 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0528.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted537_eq528, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 538 = (1085 / 101088 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 523 = (539 / 22464 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0523.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted538_eq523, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 539 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 524 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0524.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted539_eq524, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 540 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 525 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0525.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch09.weighted540_eq525, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 541 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 526 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0526.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted541_eq526, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 542 = (-19 / 3159 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 527 = (-553 / 44928 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0527.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted542_eq527, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 543 = (-67 / 12960 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 528 = (-67 / 5760 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0528.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted543_eq528, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock16_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 512 (Fin.castAdd 271 i))) = (1 / 33696 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block16 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock16 i)
    _ = _ := BlowupF1CandidateWeightedTable.block16_sum

end AxiomaticGW.BlowupF1WeightedAssembly
