/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch11
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0604
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0605
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0610
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0611
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0612
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0613
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0602
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0603
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0626
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0627
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0628
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0629
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0630
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0631
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0632
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0633
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0634
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0635
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0636
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0637
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

/-- Exact original positions 608 through 639. -/
theorem checkedBlock19 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 608 (Fin.castAdd 175 i)) =
      BlowupF1CandidateWeightedTable.block19 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 608 = (-1 / 576 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 604 = (-1 / 576 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0604.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted608_eq604, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 609 = (1 / 8640 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 605 = (1 / 8640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0605.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted609_eq605, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 610 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0610.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 611 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0611.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 612 = (1 / 960 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0612.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 613 = (1 / 960 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0613.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 614 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 602 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0602.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted614_eq602, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 615 = (-1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 603 = (1 / 8640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0603.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted615_eq603, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 616 = (-1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 604 = (-1 / 576 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0604.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted616_eq604, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 617 = (-1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 605 = (1 / 8640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0605.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted617_eq605, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 618 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 610 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0610.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted618_eq610, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 619 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 611 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0611.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted619_eq611, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 620 = (1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 612 = (1 / 960 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0612.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted620_eq612, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 621 = (1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 613 = (1 / 960 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0613.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted621_eq613, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 622 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 610 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0610.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted622_eq610, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 623 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 611 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0611.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted623_eq611, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 624 = (1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 612 = (1 / 960 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0612.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted624_eq612, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 625 = (1 / 2880 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 613 = (1 / 960 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0613.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted625_eq613, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 626 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0626.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 627 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0627.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 628 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0628.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 629 = (7 / 8640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0629.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 630 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0630.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 631 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0631.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 632 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0632.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 633 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0633.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 634 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0634.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 635 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0635.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 636 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0636.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 637 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0637.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 638 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 634 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0634.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted638_eq634, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 639 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 635 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0635.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted639_eq635, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock19_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 608 (Fin.castAdd 175 i))) = (7 / 4320 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block19 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock19 i)
    _ = _ := BlowupF1CandidateWeightedTable.block19_sum

end AxiomaticGW.BlowupF1WeightedAssembly
