/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch12
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0636
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0637
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0642
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0643
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0644
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0645
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch11
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0634
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0635
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0658
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0659
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0660
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0661
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0662
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0663
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0664
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0665
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0666
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0667
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0668
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0669
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0670
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0671
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

/-- Exact original positions 640 through 671. -/
theorem checkedBlock20 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 640 (Fin.castAdd 143 i)) =
      BlowupF1CandidateWeightedTable.block20 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 640 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 636 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0636.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted640_eq636, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 641 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 637 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0637.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted641_eq637, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 642 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0642.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 643 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0643.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 644 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0644.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 645 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0645.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 646 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 634 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0634.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted646_eq634, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 647 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 635 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0635.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted647_eq635, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 648 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 636 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0636.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted648_eq636, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 649 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 637 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0637.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted649_eq637, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 650 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 642 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0642.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted650_eq642, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 651 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 643 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0643.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted651_eq643, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 652 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 644 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0644.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted652_eq644, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 653 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 645 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0645.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted653_eq645, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 654 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 642 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0642.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted654_eq642, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 655 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 643 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0643.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted655_eq643, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 656 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 644 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0644.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted656_eq644, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 657 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 645 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0645.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted657_eq645, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 658 = (1 / 17280 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0658.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 659 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0659.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 660 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0660.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 661 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0661.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 662 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0662.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 663 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0663.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 664 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0664.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 665 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0665.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 666 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0666.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 667 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0667.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 668 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0668.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 669 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0669.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 670 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0670.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 671 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0671.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock20_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 640 (Fin.castAdd 143 i))) = (1 / 17280 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block20 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock20 i)
    _ = _ := BlowupF1CandidateWeightedTable.block20_sum

end AxiomaticGW.BlowupF1WeightedAssembly
