/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0544
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0545
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0546
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0547
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0548
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch10
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0550
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0551
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0552
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0553
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0554
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0556
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0565
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0566
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0567
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0568
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0569
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0570
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0571
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0572
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0573
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

/-- Exact original positions 544 through 575. -/
theorem checkedBlock17 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 544 (Fin.castAdd 239 i)) =
      BlowupF1CandidateWeightedTable.block17 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 544 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0544.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 545 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0545.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 546 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0546.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 547 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0547.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 548 = (1 / 360 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0548.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 549 = (1 / 360 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 548 = (1 / 360 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0548.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted549_eq548, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 550 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0550.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 551 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0551.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 552 = (-1 / 432 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0552.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 553 = (1 / 720 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0553.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 554 = (1 / 2160 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0554.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 555 = (1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 548 = (1 / 360 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0548.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted555_eq548, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 556 = (1 / 2160 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0556.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 557 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 550 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0550.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted557_eq550, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 558 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 551 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0551.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted558_eq551, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 559 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 552 = (-1 / 432 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0552.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted559_eq552, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 560 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 553 = (1 / 720 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0553.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted560_eq553, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 561 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 550 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0550.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted561_eq550, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 562 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 551 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0551.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted562_eq551, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 563 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 552 = (-1 / 432 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0552.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted563_eq552, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 564 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 553 = (1 / 720 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0553.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted564_eq553, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 565 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0565.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 566 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0566.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 567 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0567.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 568 = (-1 / 240 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0568.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 569 = (1 / 360 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0569.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 570 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0570.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 571 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0571.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 572 = (1 / 720 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0572.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 573 = (-1 / 432 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0573.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 574 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 570 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0570.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted574_eq570, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 575 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 571 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0571.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted575_eq571, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock17_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 544 (Fin.castAdd 239 i))) = (1 / 540 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block17 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock17 i)
    _ = _ := BlowupF1CandidateWeightedTable.block17_sum

end AxiomaticGW.BlowupF1WeightedAssembly
