/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch10
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0572
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0573
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0578
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0579
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0580
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0581
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0570
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0571
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch11
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0594
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0595
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0596
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0597
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0598
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0599
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0600
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0601
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0602
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0603
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0604
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0605
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

/-- Exact original positions 576 through 607. -/
theorem checkedBlock18 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 576 (Fin.castAdd 207 i)) =
      BlowupF1CandidateWeightedTable.block18 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 576 = (1 / 720 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 572 = (1 / 720 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0572.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted576_eq572, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 577 = (-1 / 432 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 573 = (-1 / 432 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0573.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted577_eq573, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 578 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0578.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 579 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0579.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 580 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0580.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 581 = (-1 / 80 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0581.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 582 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 570 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0570.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted582_eq570, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 583 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 571 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0571.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted583_eq571, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 584 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 572 = (1 / 720 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0572.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted584_eq572, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 585 = (-1 / 2160 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 573 = (-1 / 432 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0573.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted585_eq573, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 586 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 578 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0578.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted586_eq578, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 587 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 579 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0579.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted587_eq579, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 588 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 580 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0580.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted588_eq580, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 589 = (-1 / 240 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 581 = (-1 / 80 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0581.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted589_eq581, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 590 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 578 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0578.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch10.weighted590_eq578, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 591 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 579 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0579.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted591_eq579, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 592 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 580 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0580.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted592_eq580, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 593 = (-1 / 240 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 581 = (-1 / 80 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0581.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted593_eq581, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 594 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0594.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 595 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0595.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 596 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0596.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 597 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0597.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 598 = (-1 / 8640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0598.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 599 = (-1 / 960 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0599.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 600 = (-1 / 8640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0600.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 601 = (-1 / 8640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0601.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 602 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0602.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 603 = (1 / 8640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0603.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 604 = (-1 / 576 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0604.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 605 = (1 / 8640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0605.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 606 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 602 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0602.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted606_eq602, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 607 = (1 / 8640 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 603 = (1 / 8640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0603.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch11.weighted607_eq603, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock18_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 576 (Fin.castAdd 207 i))) = (-11 / 432 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block18 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock18 i)
    _ = _ := BlowupF1CandidateWeightedTable.block18_sum

end AxiomaticGW.BlowupF1WeightedAssembly
