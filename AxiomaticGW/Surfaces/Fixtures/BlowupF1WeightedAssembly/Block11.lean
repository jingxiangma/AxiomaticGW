/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch05
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0331
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0332
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0333
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0334
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0335
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0336
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0337
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0338
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0339
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0361
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0362
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0363
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0364
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch04
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0323
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0329
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0330
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0377Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0378
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0379Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0380
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0381Ordered
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0382
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRepresentative0383Ordered
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

/-- Exact original positions 352 through 383. -/
theorem checkedBlock11 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 352 (Fin.castAdd 431 i)) =
      BlowupF1CandidateWeightedTable.block11 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 352 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 331 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0331.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted352_eq331, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 353 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 332 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0332.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted353_eq332, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 354 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 333 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0333.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted354_eq333, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 355 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 334 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0334.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted355_eq334, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 356 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 335 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0335.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted356_eq335, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 357 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 336 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0336.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted357_eq336, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 358 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 337 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0337.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted358_eq337, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 359 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 338 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0338.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted359_eq338, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 360 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 339 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0339.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted360_eq339, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 361 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0361.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 362 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0362.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 363 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0363.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 364 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0364.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 365 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 323 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0323.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted365_eq323, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 366 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 323 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0323.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted366_eq323, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 367 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 329 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0329.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch04.weighted367_eq329, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 368 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 330 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0330.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted368_eq330, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 369 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 331 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0331.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted369_eq331, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 370 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 332 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0332.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted370_eq332, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 371 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 361 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0361.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted371_eq361, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 372 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 362 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0362.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted372_eq362, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 373 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 363 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0363.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted373_eq363, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 374 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 361 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0361.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted374_eq361, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 375 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 362 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0362.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted375_eq362, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 376 = 0
    have hr : BlowupF1RootAssembly.originalWeighted 363 = 0 :=
      AxiomaticGW.BlowupF1FullRootReplay.Representative0363.original_eq_claimed
    rw [AxiomaticGW.BlowupF1RootRelabelTransfers.Batch05.weighted376_eq363, hr]
    norm_num
  · change BlowupF1RootAssembly.originalWeighted 377 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0377.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 378 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0378.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 379 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0379.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 380 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0380.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 381 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0381.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 382 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0382.original_eq_claimed
  · change BlowupF1RootAssembly.originalWeighted 383 = 0
    exact AxiomaticGW.BlowupF1FullRootReplay.Representative0383.original_eq_claimed

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock11_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 352 (Fin.castAdd 431 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block11 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock11 i)
    _ = _ := BlowupF1CandidateWeightedTable.block11_sum

end AxiomaticGW.BlowupF1WeightedAssembly
