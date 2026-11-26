/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CandidateWeightedTable
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch00
import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.CoefficientBatch01
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

/-- Exact original positions 0 through 31. -/
theorem checkedBlock00 (i : Fin 32) :
    BlowupF1RootAssembly.originalWeighted (Fin.natAdd 0 (Fin.castAdd 783 i)) =
      BlowupF1CandidateWeightedTable.block00 i := by
  fin_cases i
  · change BlowupF1RootAssembly.originalWeighted 0 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted0
  · change BlowupF1RootAssembly.originalWeighted 1 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted1
  · change BlowupF1RootAssembly.originalWeighted 2 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted2
  · change BlowupF1RootAssembly.originalWeighted 3 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted3
  · change BlowupF1RootAssembly.originalWeighted 4 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted4
  · change BlowupF1RootAssembly.originalWeighted 5 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted5
  · change BlowupF1RootAssembly.originalWeighted 6 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted6
  · change BlowupF1RootAssembly.originalWeighted 7 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted7
  · change BlowupF1RootAssembly.originalWeighted 8 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted8
  · change BlowupF1RootAssembly.originalWeighted 9 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted9
  · change BlowupF1RootAssembly.originalWeighted 10 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted10
  · change BlowupF1RootAssembly.originalWeighted 11 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted11
  · change BlowupF1RootAssembly.originalWeighted 12 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted12
  · change BlowupF1RootAssembly.originalWeighted 13 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted13
  · change BlowupF1RootAssembly.originalWeighted 14 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted14
  · change BlowupF1RootAssembly.originalWeighted 15 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted15
  · change BlowupF1RootAssembly.originalWeighted 16 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted16
  · change BlowupF1RootAssembly.originalWeighted 17 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted17
  · change BlowupF1RootAssembly.originalWeighted 18 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted18
  · change BlowupF1RootAssembly.originalWeighted 19 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted19
  · change BlowupF1RootAssembly.originalWeighted 20 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted20
  · change BlowupF1RootAssembly.originalWeighted 21 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted21
  · change BlowupF1RootAssembly.originalWeighted 22 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted22
  · change BlowupF1RootAssembly.originalWeighted 23 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted23
  · change BlowupF1RootAssembly.originalWeighted 24 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00.weighted24
  · change BlowupF1RootAssembly.originalWeighted 25 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted25
  · change BlowupF1RootAssembly.originalWeighted 26 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted26
  · change BlowupF1RootAssembly.originalWeighted 27 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted27
  · change BlowupF1RootAssembly.originalWeighted 28 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted28
  · change BlowupF1RootAssembly.originalWeighted 29 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted29
  · change BlowupF1RootAssembly.originalWeighted 30 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted30
  · change BlowupF1RootAssembly.originalWeighted 31 = 0
    exact AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch01.weighted31

/-- Sum the checked original interval without evaluating its component backend. -/
theorem originalBlock00_sum :
    (∑ i : Fin 32, BlowupF1RootAssembly.originalWeighted
      (Fin.natAdd 0 (Fin.castAdd 783 i))) = 0 := by
  calc
    _ = ∑ i : Fin 32, BlowupF1CandidateWeightedTable.block00 i :=
      Finset.sum_congr rfl (fun i _ ↦ checkedBlock00 i)
    _ = _ := BlowupF1CandidateWeightedTable.block00_sum

end AxiomaticGW.BlowupF1WeightedAssembly
