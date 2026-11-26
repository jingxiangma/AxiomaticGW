/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.GuardBatch00
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch02
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch03
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

/-- Exact original positions 64 through 95. -/
theorem checkedBlock02 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 64 (Fin.castAdd 719 i)) =
      BlowupF1CandidateWeightedTable.block02 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 64 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted64
  · change BlowupF1RootAssembly.originalWeighted 65 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted65
  · change BlowupF1RootAssembly.originalWeighted 66 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted66
  · change BlowupF1RootAssembly.originalWeighted 67 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted67
  · change BlowupF1RootAssembly.originalWeighted 68 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted68
  · change BlowupF1RootAssembly.originalWeighted 69 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted69
  · change BlowupF1RootAssembly.originalWeighted 70 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted70
  · change BlowupF1RootAssembly.originalWeighted 71 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted71
  · change BlowupF1RootAssembly.originalWeighted 72 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted72
  · change BlowupF1RootAssembly.originalWeighted 73 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted73
  · change BlowupF1RootAssembly.originalWeighted 74 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted74
  · change BlowupF1RootAssembly.originalWeighted 75 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted75
  · change BlowupF1RootAssembly.originalWeighted 76 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted76
  · change BlowupF1RootAssembly.originalWeighted 77 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted77
  · change BlowupF1RootAssembly.originalWeighted 78 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted78
  · change BlowupF1RootAssembly.originalWeighted 79 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted79
  · change BlowupF1RootAssembly.originalWeighted 80 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted80
  · change BlowupF1RootAssembly.originalWeighted 81 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted81
  · change BlowupF1RootAssembly.originalWeighted 82 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted82
  · change BlowupF1RootAssembly.originalWeighted 83 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted83
  · change BlowupF1RootAssembly.originalWeighted 84 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted84
  · change BlowupF1RootAssembly.originalWeighted 85 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted85
  · change BlowupF1RootAssembly.originalWeighted 86 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted86
  · change BlowupF1RootAssembly.originalWeighted 87 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted87
  · change BlowupF1RootAssembly.originalWeighted 88 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted88
  · change BlowupF1RootAssembly.originalWeighted 89 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted89
  · change BlowupF1RootAssembly.originalWeighted 90 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02.weighted90
  · change BlowupF1RootAssembly.originalWeighted 91 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted91
  · change BlowupF1RootAssembly.originalWeighted 92 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted92
  · change BlowupF1RootAssembly.originalWeighted 93 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted93
  · change BlowupF1RootAssembly.originalWeighted 94 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch03.weighted94
  · change BlowupF1RootAssembly.originalWeighted 95 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.GuardBatch00.weighted95

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock02_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 64 (Fin.castAdd 719 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block02 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock02 i)
    _ = _ := BlowupF1CandidateWeightedTable.block02_sum

end AxiomaticGW.BlowupF1WeightedAssembly
