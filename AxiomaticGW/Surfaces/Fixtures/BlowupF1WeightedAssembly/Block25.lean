/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch15
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0766
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch16
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0767
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0768
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0769
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0770
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0805
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0808
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0809
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0811
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

/-- Exact original positions 800 through 814. -/
theorem checkedBlock25 (i : Fin 15) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 800 (Fin.castAdd 0 i)) =
      BlowupF1CandidateWeightedTable.block25 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 800 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 766 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0766.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch15.weighted800_eq766, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 801 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 767 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0767.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted801_eq767, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 802 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 768 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0768.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted802_eq768, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 803 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 769 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0769.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted803_eq769, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 804 = (187 / 134784 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 770 = (227 / 74880 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0770.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted804_eq770, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 805 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0805.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 806 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 805 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0805.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted806_eq805, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 807 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 805 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0805.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted807_eq805, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 808 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0808.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 809 = (-77 / 112320 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0809.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 810 = (-77 / 112320 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 809 = (-77 / 112320 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0809.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted810_eq809, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 811 = (77 / 37440 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0811.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 812 = (-77 / 168480 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 809 = (-77 / 112320 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0809.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted812_eq809, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 813 = (31 / 33696 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 811 = (77 / 37440 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0811.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted813_eq811, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 814 = (31 / 33696 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 811 = (77 / 37440 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0811.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch16.weighted814_eq811, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock25_sum :
    (∑ i : Fin 15, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 800 (Fin.castAdd 0 i))) = (2329 / 673920 : ℚ) := by
  calc
    _ = ∑ i : Fin 15, BlowupF1CandidateWeightedTable.block25 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock25 i)
    _ = _ := BlowupF1CandidateWeightedTable.block25_sum

end AxiomaticGW.BlowupF1WeightedAssembly
