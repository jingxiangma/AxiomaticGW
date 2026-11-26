/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0736
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0737
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0738
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0739
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0740
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch15
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0743
import AxiomaticGW.Surfaces.Fixtures.BlowupF1SelectedRootPilot0744
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch14
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0727
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0729
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0730
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0731
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0732
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0735
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0763
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0764
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0765
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0766
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

/-- Exact original positions 736 through 767. -/
theorem checkedBlock23 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 736 (Fin.castAdd 47 i)) =
      BlowupF1CandidateWeightedTable.block23 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 736 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0736.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 737 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0737.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 738 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0738.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 739 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0739.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 740 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0740.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 741 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 739 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0739.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted741_eq739, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 742 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 740 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0740.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted742_eq740, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 743 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0743.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 744 = (-227 / 224640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.SelectedPilot0744.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 745 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 727 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0727.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted745_eq727, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 746 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 727 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0727.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted746_eq727, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 747 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 729 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0729.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted747_eq729, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 748 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 730 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0730.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted748_eq730, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 749 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 731 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0731.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted749_eq731, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 750 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 732 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0732.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted750_eq732, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 751 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 731 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0731.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted751_eq731, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 752 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 732 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0732.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted752_eq732, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 753 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 735 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0735.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted753_eq735, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 754 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 736 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0736.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted754_eq736, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 755 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 737 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0737.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch14.weighted755_eq737, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 756 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 738 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0738.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted756_eq738, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 757 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 739 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0739.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted757_eq739, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 758 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 740 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0740.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted758_eq740, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 759 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 739 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0739.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted759_eq739, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 760 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 740 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0740.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted760_eq740, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 761 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 743 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0743.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted761_eq743, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 762 = (-227 / 224640 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 744 = (-227 / 224640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.SelectedPilot0744.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted762_eq744, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 763 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0763.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 764 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0764.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 765 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0765.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 766 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0766.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 767 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0767.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock23_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 736 (Fin.castAdd 47 i))) = (-227 / 112320 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block23 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock23 i)
    _ = _ := BlowupF1CandidateWeightedTable.block23_sum

end AxiomaticGW.BlowupF1WeightedAssembly
