/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch01
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch02
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.GuardBatch00
public import Mathlib.Tactic.FinCases

/-! # Checked interval of the original weighted F1 contraction

Every position reuses its accepted zero or representative theorem, or the
original structural coefficient-ratio transfer followed by its representative.
The component evaluator is never unfolded by this assembly.
-/

@[expose] public section
set_option autoImplicit false
namespace AxiomaticGW.BlowupF1WeightedAssembly
open scoped BigOperators

/-- Exact original positions 32 through 63. -/
theorem checkedBlock01 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 32 (Fin.castAdd 751 i)) =
      BlowupF1CandidateWeightedTable.block01 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 32 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted32
  · change BlowupF1RootAssembly.originalWeighted 33 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted33
  · change BlowupF1RootAssembly.originalWeighted 34 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted34
  · change BlowupF1RootAssembly.originalWeighted 35 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted35
  · change BlowupF1RootAssembly.originalWeighted 36 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted36
  · change BlowupF1RootAssembly.originalWeighted 37 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted37
  · change BlowupF1RootAssembly.originalWeighted 38 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted38
  · change BlowupF1RootAssembly.originalWeighted 39 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted39
  · change BlowupF1RootAssembly.originalWeighted 40 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted40
  · change BlowupF1RootAssembly.originalWeighted 41 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted41
  · change BlowupF1RootAssembly.originalWeighted 42 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted42
  · change BlowupF1RootAssembly.originalWeighted 43 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted43
  · change BlowupF1RootAssembly.originalWeighted 44 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted44
  · change BlowupF1RootAssembly.originalWeighted 45 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted45
  · change BlowupF1RootAssembly.originalWeighted 46 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted46
  · change BlowupF1RootAssembly.originalWeighted 47 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted47
  · change BlowupF1RootAssembly.originalWeighted 48 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted48
  · change BlowupF1RootAssembly.originalWeighted 49 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted49
  · change BlowupF1RootAssembly.originalWeighted 50 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted50
  · change BlowupF1RootAssembly.originalWeighted 51 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted51
  · change BlowupF1RootAssembly.originalWeighted 52 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted52
  · change BlowupF1RootAssembly.originalWeighted 53 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted53
  · change BlowupF1RootAssembly.originalWeighted 54 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted54
  · change BlowupF1RootAssembly.originalWeighted 55 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted55
  · change BlowupF1RootAssembly.originalWeighted 56 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted56
  · change BlowupF1RootAssembly.originalWeighted 57 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted57
  · change BlowupF1RootAssembly.originalWeighted 58 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted58
  · change BlowupF1RootAssembly.originalWeighted 59 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted59
  · change BlowupF1RootAssembly.originalWeighted 60 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted60
  · change BlowupF1RootAssembly.originalWeighted 61 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted61
  · change BlowupF1RootAssembly.originalWeighted 62 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted62
  · change BlowupF1RootAssembly.originalWeighted 63 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted63

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock01_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 32 (Fin.castAdd 751 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block01 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock01 i)
    _ = _ := BlowupF1CandidateWeightedTable.block01_sum

end AxiomaticGW.BlowupF1WeightedAssembly
