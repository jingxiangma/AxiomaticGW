/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch06
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0409Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0417
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0418
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0419
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0420
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0421
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0422
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0423
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0424
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0425
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0426
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch07
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0447
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

/-- Exact original positions 416 through 447. -/
theorem checkedBlock13 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 416 (Fin.castAdd 367 i)) =
      BlowupF1CandidateWeightedTable.block13 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 416 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 409 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0409.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch06.weighted416_eq409, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 417 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0417.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 418 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0418.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 419 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0419.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 420 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0420.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 421 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0421.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 422 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0422.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 423 = (-73 / 56160 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0423.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 424 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0424.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 425 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0425.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 426 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0426.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 427 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 417 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0417.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted427_eq417, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 428 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 418 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0418.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted428_eq418, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 429 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 419 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0419.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted429_eq419, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 430 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 420 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0420.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted430_eq420, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 431 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 421 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0421.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted431_eq421, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 432 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 422 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0422.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted432_eq422, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 433 = (-73 / 84240 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 423 = (-73 / 56160 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0423.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted433_eq423, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 434 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 424 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0424.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted434_eq424, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 435 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 425 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0425.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted435_eq425, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 436 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 426 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0426.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted436_eq426, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 437 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 417 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0417.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted437_eq417, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 438 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 418 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0418.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted438_eq418, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 439 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 419 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0419.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted439_eq419, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 440 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 420 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0420.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted440_eq420, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 441 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 421 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0421.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted441_eq421, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 442 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 422 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0422.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted442_eq422, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 443 = (-73 / 84240 : ℚ)
    have hr : BlowupF1RootAssembly.originalWeighted 423 = (-73 / 56160 : ℚ) :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0423.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted443_eq423, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 444 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 424 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0424.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted444_eq424, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 445 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 425 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0425.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted445_eq425, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 446 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 426 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0426.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch07.weighted446_eq426, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 447 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0447.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock13_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 416 (Fin.castAdd 367 i))) = (-511 / 168480 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block13 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock13 i)
    _ = _ := BlowupF1CandidateWeightedTable.block13_sum

end AxiomaticGW.BlowupF1WeightedAssembly
