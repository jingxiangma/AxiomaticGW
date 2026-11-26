/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch05
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0377Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0378
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch06
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0379Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0380
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0381Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0382
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0383Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0398Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0399Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0400
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0403Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0409Ordered
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

/-- Exact original positions 384 through 415. -/
theorem checkedBlock12 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 384 (Fin.castAdd 399 i)) =
      BlowupF1CandidateWeightedTable.block12 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 384 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 377 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0377.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted384_eq377, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 385 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 378 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0378.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted385_eq378, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 386 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 379 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0379.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted386_eq379, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 387 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 380 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0380.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted387_eq380, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 388 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 381 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0381.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted388_eq381, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 389 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 382 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0382.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted389_eq382, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 390 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 383 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0383.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted390_eq383, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 391 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 377 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0377.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted391_eq377, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 392 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 378 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0378.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted392_eq378, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 393 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 379 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0379.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted393_eq379, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 394 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 380 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0380.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted394_eq380, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 395 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 381 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0381.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted395_eq381, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 396 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 382 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0382.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted396_eq382, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 397 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 383 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0383.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted397_eq383, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 398 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0398.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 399 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0399.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 400 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0400.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 401 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 399 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0399.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted401_eq399, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 402 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 400 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0400.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted402_eq400, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 403 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0403.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 404 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 399 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0399.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted404_eq399, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 405 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 400 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0400.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted405_eq400, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 406 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 399 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0399.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted406_eq399, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 407 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 400 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0400.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted407_eq400, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 408 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 403 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0403.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted408_eq403, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 409 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0409.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 410 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 399 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0399.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted410_eq399, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 411 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 400 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0400.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted411_eq400, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 412 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 399 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0399.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted412_eq399, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 413 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 400 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0400.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted413_eq400, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 414 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 403 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0403.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted414_eq403, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 415 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 409 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0409.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted415_eq409, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock12_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 384 (Fin.castAdd 399 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block12 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock12 i)
    _ = _ := BlowupF1CandidateWeightedTable.block12_sum

end AxiomaticGW.BlowupF1WeightedAssembly
