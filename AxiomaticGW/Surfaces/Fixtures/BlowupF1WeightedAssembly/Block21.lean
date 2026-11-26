/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0672
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0673
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0674
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0675
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0676
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0677
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0678
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0679
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0680
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch12
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0662
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0663
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0664
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0665
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0666
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0667
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch13
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

/-- Exact original positions 672 through 703. -/
theorem checkedBlock21 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 672 (Fin.castAdd 111 i)) =
      BlowupF1CandidateWeightedTable.block21 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 672 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0672.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 673 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0673.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 674 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0674.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 675 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0675.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 676 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0676.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 677 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0677.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 678 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0678.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 679 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0679.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 680 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0680.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 681 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 662 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0662.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted681_eq662, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 682 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 663 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0663.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted682_eq663, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 683 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 664 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0664.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted683_eq664, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 684 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 665 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0665.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted684_eq665, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 685 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 666 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0666.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted685_eq666, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 686 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 667 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0667.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted686_eq667, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 687 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 668 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0668.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted687_eq668, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 688 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 669 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0669.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted688_eq669, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 689 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 670 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0670.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted689_eq670, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 690 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 671 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0671.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted690_eq671, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 691 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 672 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0672.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted691_eq672, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 692 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 673 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0673.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted692_eq673, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 693 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 674 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0674.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted693_eq674, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 694 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 675 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0675.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted694_eq675, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 695 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 676 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0676.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted695_eq676, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 696 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 677 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0677.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted696_eq677, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 697 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 678 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0678.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted697_eq678, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 698 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 679 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0679.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted698_eq679, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 699 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 680 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0680.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted699_eq680, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 700 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 662 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0662.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted700_eq662, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 701 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 663 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0663.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted701_eq663, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 702 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 664 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0664.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted702_eq664, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 703 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 665 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0665.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted703_eq665, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock21_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 672 (Fin.castAdd 111 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block21 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock21 i)
    _ = _ := BlowupF1CandidateWeightedTable.block21_sum

end AxiomaticGW.BlowupF1WeightedAssembly
