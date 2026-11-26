/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0320
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0321
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0322
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0323
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0324
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0325
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch04
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0329
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0330
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0331
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0332
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0333
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0334
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0335
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0336
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0337
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0338
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0339
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch05
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

/-- Exact original positions 320 through 351. -/
theorem checkedBlock10 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 320 (Fin.castAdd 463 i)) =
      BlowupF1CandidateWeightedTable.block10 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 320 = (1 / 480 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0320.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 321 = (1 / 4320 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0321.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 322 = (1 / 4320 : ℚ)
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0322.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 323 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0323.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 324 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0324.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 325 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0325.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 326 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 323 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0323.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted326_eq323, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 327 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 324 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0324.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted327_eq324, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 328 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 325 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0325.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted328_eq325, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 329 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0329.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 330 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0330.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 331 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0331.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 332 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0332.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 333 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0333.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 334 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0334.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 335 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0335.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 336 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0336.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 337 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0337.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 338 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0338.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 339 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0339.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 340 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 336 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0336.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted340_eq336, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 341 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 337 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0337.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted341_eq337, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 342 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 338 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0338.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted342_eq338, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 343 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 339 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0339.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted343_eq339, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 344 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 323 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0323.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted344_eq323, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 345 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 324 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0324.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted345_eq324, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 346 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 325 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0325.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted346_eq325, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 347 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 323 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0323.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted347_eq323, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 348 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 324 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0324.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted348_eq324, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 349 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 325 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0325.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted349_eq325, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 350 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 329 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0329.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted350_eq329, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 351 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 330 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0330.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted351_eq330, hr]
    norm_num

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock10_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 320 (Fin.castAdd 463 i))) = (11 / 4320 : ℚ) := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block10 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock10 i)
    _ = _ := BlowupF1CandidateWeightedTable.block10_sum

end AxiomaticGW.BlowupF1WeightedAssembly
