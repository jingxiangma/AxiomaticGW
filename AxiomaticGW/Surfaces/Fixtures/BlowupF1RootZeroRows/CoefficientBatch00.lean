/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Original F1 rows killed by exact coordinates or the existing genus guard

Each original relation coordinate and required genus bound is checked against
the actual definitions. The statements concern the existing guarded contraction;
they do not assert vanishing of the unguarded contraction.
No sampled component value, native zero, or geometric premise is used.
-/

@[expose] public section
set_option Elab.async false

namespace AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00

open BlowupF1RootAssembly

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient0 : L24CorrectionsReplay.fullClaim 0 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted0 : originalWeighted 0 = 0 :=
  originalWeighted_eq_zero_of_coefficient 0 coefficient0

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient1 : L24CorrectionsReplay.fullClaim 1 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted1 : originalWeighted 1 = 0 :=
  originalWeighted_eq_zero_of_coefficient 1 coefficient1

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient2 : L24CorrectionsReplay.fullClaim 2 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted2 : originalWeighted 2 = 0 :=
  originalWeighted_eq_zero_of_coefficient 2 coefficient2

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient3 : L24CorrectionsReplay.fullClaim 3 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted3 : originalWeighted 3 = 0 :=
  originalWeighted_eq_zero_of_coefficient 3 coefficient3

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient4 : L24CorrectionsReplay.fullClaim 4 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted4 : originalWeighted 4 = 0 :=
  originalWeighted_eq_zero_of_coefficient 4 coefficient4

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient5 : L24CorrectionsReplay.fullClaim 5 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted5 : originalWeighted 5 = 0 :=
  originalWeighted_eq_zero_of_coefficient 5 coefficient5

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient6 : L24CorrectionsReplay.fullClaim 6 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted6 : originalWeighted 6 = 0 :=
  originalWeighted_eq_zero_of_coefficient 6 coefficient6

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient7 : L24CorrectionsReplay.fullClaim 7 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted7 : originalWeighted 7 = 0 :=
  originalWeighted_eq_zero_of_coefficient 7 coefficient7

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient8 : L24CorrectionsReplay.fullClaim 8 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted8 : originalWeighted 8 = 0 :=
  originalWeighted_eq_zero_of_coefficient 8 coefficient8

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient9 : L24CorrectionsReplay.fullClaim 9 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted9 : originalWeighted 9 = 0 :=
  originalWeighted_eq_zero_of_coefficient 9 coefficient9

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient10 : L24CorrectionsReplay.fullClaim 10 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted10 : originalWeighted 10 = 0 :=
  originalWeighted_eq_zero_of_coefficient 10 coefficient10

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient11 : L24CorrectionsReplay.fullClaim 11 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted11 : originalWeighted 11 = 0 :=
  originalWeighted_eq_zero_of_coefficient 11 coefficient11

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient12 : L24CorrectionsReplay.fullClaim 12 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted12 : originalWeighted 12 = 0 :=
  originalWeighted_eq_zero_of_coefficient 12 coefficient12

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient13 : L24CorrectionsReplay.fullClaim 13 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted13 : originalWeighted 13 = 0 :=
  originalWeighted_eq_zero_of_coefficient 13 coefficient13

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient14 : L24CorrectionsReplay.fullClaim 14 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted14 : originalWeighted 14 = 0 :=
  originalWeighted_eq_zero_of_coefficient 14 coefficient14

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient15 : L24CorrectionsReplay.fullClaim 15 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted15 : originalWeighted 15 = 0 :=
  originalWeighted_eq_zero_of_coefficient 15 coefficient15

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient16 : L24CorrectionsReplay.fullClaim 16 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted16 : originalWeighted 16 = 0 :=
  originalWeighted_eq_zero_of_coefficient 16 coefficient16

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient17 : L24CorrectionsReplay.fullClaim 17 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted17 : originalWeighted 17 = 0 :=
  originalWeighted_eq_zero_of_coefficient 17 coefficient17

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient18 : L24CorrectionsReplay.fullClaim 18 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted18 : originalWeighted 18 = 0 :=
  originalWeighted_eq_zero_of_coefficient 18 coefficient18

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient19 : L24CorrectionsReplay.fullClaim 19 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted19 : originalWeighted 19 = 0 :=
  originalWeighted_eq_zero_of_coefficient 19 coefficient19

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient20 : L24CorrectionsReplay.fullClaim 20 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted20 : originalWeighted 20 = 0 :=
  originalWeighted_eq_zero_of_coefficient 20 coefficient20

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient21 : L24CorrectionsReplay.fullClaim 21 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted21 : originalWeighted 21 = 0 :=
  originalWeighted_eq_zero_of_coefficient 21 coefficient21

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient22 : L24CorrectionsReplay.fullClaim 22 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted22 : originalWeighted 22 = 0 :=
  originalWeighted_eq_zero_of_coefficient 22 coefficient22

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient23 : L24CorrectionsReplay.fullClaim 23 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted23 : originalWeighted 23 = 0 :=
  originalWeighted_eq_zero_of_coefficient 23 coefficient23

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient24 : L24CorrectionsReplay.fullClaim 24 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted24 : originalWeighted 24 = 0 :=
  originalWeighted_eq_zero_of_coefficient 24 coefficient24

end AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch00
