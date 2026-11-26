/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0768
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0769
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0770
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch14
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0727
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0729
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0730
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0731
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0732
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0735
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0736
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch15
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0737
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0738
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0739
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0740
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0743
import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedRootPilot0744
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0763
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0764
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0765
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0766
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch16
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0767
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

/-- Exact original positions 768 through 799. -/
theorem checkedBlock24 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 768 (Fin.castAdd 15 i)) =
      BlowupF1CandidateWeightedTable.block24 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 768 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0768.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 769 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0769.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 770 = (227 / 74880 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0770.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 771 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 727 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0727.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted771_eq727, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 772 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 727 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0727.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted772_eq727, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 773 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 729 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0729.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted773_eq729, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 774 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 730 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0730.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted774_eq730, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 775 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 731 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0731.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted775_eq731, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 776 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 732 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0732.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted776_eq732, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 777 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 731 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0731.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted777_eq731, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 778 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 732 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0732.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted778_eq732, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 779 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 735 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0735.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted779_eq735, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 780 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 736 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0736.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted780_eq736, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 781 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 737 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0737.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted781_eq737, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 782 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 738 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0738.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted782_eq738, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 783 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 739 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0739.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted783_eq739, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 784 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 740 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0740.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted784_eq740, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 785 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 739 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0739.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted785_eq739, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 786 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 740 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0740.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted786_eq740, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 787 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 743 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0743.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted787_eq743, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 788 = (-227 / 336960 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 744 = (-227 / 224640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.SelectedPilot0744.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted788_eq744, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 789 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 763 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0763.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted789_eq763, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 790 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 764 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0764.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted790_eq764, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 791 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 765 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0765.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted791_eq765, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 792 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 766 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0766.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted792_eq766, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 793 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 767 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0767.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted793_eq767, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 794 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 768 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0768.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted794_eq768, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 795 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 769 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0769.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted795_eq769, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 796 = (187 / 134784 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 770 = (227 / 74880 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0770.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted796_eq770, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 797 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 763 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0763.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted797_eq763, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 798 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 764 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0764.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted798_eq764, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 799 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 765 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0765.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted799_eq765, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock24_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 768 (Fin.castAdd 15 i))) = (631 / 168480 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block24 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock24 i)
    _ = _ := BlowupF1CandidateWeightedTable.block24_sum

end AxiomaticGW.BlowupF1WeightedAssembly
