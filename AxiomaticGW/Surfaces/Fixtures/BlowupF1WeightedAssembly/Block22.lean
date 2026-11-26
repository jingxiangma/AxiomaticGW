/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch12
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0666
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0667
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch13
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0668
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0669
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0670
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0671
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0672
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0673
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0674
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0675
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0676
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0677
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0678
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0679
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch14
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0680
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0719
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0720
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0721
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0722
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0723
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0724
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0725
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0726
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0727
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0729
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0730
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0731
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0732
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0735
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

/-- Exact original positions 704 through 735. -/
theorem checkedBlock22 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 704 (Fin.castAdd 79 i)) =
      BlowupF1CandidateWeightedTable.block22 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 704 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 666 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0666.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted704_eq666, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 705 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 667 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0667.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch12.weighted705_eq667, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 706 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 668 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0668.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted706_eq668, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 707 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 669 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0669.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted707_eq669, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 708 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 670 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0670.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted708_eq670, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 709 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 671 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0671.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted709_eq671, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 710 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 672 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0672.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted710_eq672, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 711 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 673 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0673.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted711_eq673, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 712 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 674 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0674.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted712_eq674, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 713 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 675 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0675.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted713_eq675, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 714 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 676 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0676.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted714_eq676, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 715 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 677 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0677.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted715_eq677, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 716 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 678 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0678.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted716_eq678, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 717 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 679 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0679.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch13.weighted717_eq679, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 718 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 680 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0680.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted718_eq680, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 719 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0719.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 720 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0720.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 721 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0721.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 722 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0722.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 723 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0723.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 724 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0724.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 725 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0725.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 726 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0726.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 727 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0727.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 728 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 727 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0727.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted728_eq727, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 729 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0729.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 730 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0730.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 731 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0731.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 732 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0732.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 733 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 731 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0731.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted733_eq731, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 734 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 732 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0732.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted734_eq732, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 735 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0735.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock22_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 704 (Fin.castAdd 79 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block22 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock22 i)
    _ = _ := BlowupF1CandidateWeightedTable.block22_sum

end AxiomaticGW.BlowupF1WeightedAssembly
