/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0448
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0449
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0450
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0451
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0452
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch07
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch08
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0455
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0456
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0457
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0459
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0470
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0471
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0472
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

/-- Exact original positions 448 through 479. -/
theorem checkedBlock14 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 448 (Fin.castAdd 335 i)) =
      BlowupF1CandidateWeightedTable.block14 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 448 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0448.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 449 = (7 / 3744 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0449.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 450 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0450.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 451 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0451.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 452 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0452.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 453 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 451 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0451.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted453_eq451, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 454 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 452 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0452.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted454_eq452, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 455 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0455.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 456 = (-73 / 224640 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0456.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 457 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0457.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 458 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 457 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0457.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted458_eq457, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 459 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0459.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 460 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 450 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0450.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted460_eq450, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 461 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 451 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0451.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted461_eq451, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 462 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 452 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0452.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted462_eq452, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 463 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 451 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0451.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted463_eq451, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 464 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 452 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0452.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted464_eq452, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 465 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 455 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0455.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted465_eq455, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 466 = (-73 / 224640 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 456 = (-73 / 224640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0456.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted466_eq456, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 467 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 457 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0457.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted467_eq457, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 468 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 457 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0457.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted468_eq457, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 469 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 459 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0459.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted469_eq459, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 470 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0470.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 471 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0471.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 472 = (73 / 74880 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0472.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 473 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 450 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0450.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted473_eq450, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 474 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 451 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0451.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted474_eq451, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 475 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 452 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0452.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted475_eq452, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 476 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 451 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0451.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted476_eq451, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 477 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 452 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0452.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted477_eq452, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 478 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 455 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0455.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted478_eq455, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 479 = (-73 / 336960 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 456 = (-73 / 224640 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0456.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch08.weighted479_eq456, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock14_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 448 (Fin.castAdd 335 i))) = (1333 / 673920 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block14 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock14 i)
    _ = _ := BlowupF1CandidateWeightedTable.block14_sum

end AxiomaticGW.BlowupF1WeightedAssembly
