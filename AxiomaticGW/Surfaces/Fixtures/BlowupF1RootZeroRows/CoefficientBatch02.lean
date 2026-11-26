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

namespace AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02

open BlowupF1RootAssembly

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient50 : L24CorrectionsReplay.fullClaim 50 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted50 : originalWeighted 50 = 0 :=
  originalWeighted_eq_zero_of_coefficient 50 coefficient50

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient53 : L24CorrectionsReplay.fullClaim 53 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted53 : originalWeighted 53 = 0 :=
  originalWeighted_eq_zero_of_coefficient 53 coefficient53

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient54 : L24CorrectionsReplay.fullClaim 54 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted54 : originalWeighted 54 = 0 :=
  originalWeighted_eq_zero_of_coefficient 54 coefficient54

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient55 : L24CorrectionsReplay.fullClaim 55 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted55 : originalWeighted 55 = 0 :=
  originalWeighted_eq_zero_of_coefficient 55 coefficient55

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient58 : L24CorrectionsReplay.fullClaim 58 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted58 : originalWeighted 58 = 0 :=
  originalWeighted_eq_zero_of_coefficient 58 coefficient58

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient60 : L24CorrectionsReplay.fullClaim 60 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted60 : originalWeighted 60 = 0 :=
  originalWeighted_eq_zero_of_coefficient 60 coefficient60

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient61 : L24CorrectionsReplay.fullClaim 61 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted61 : originalWeighted 61 = 0 :=
  originalWeighted_eq_zero_of_coefficient 61 coefficient61

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient65 : L24CorrectionsReplay.fullClaim 65 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted65 : originalWeighted 65 = 0 :=
  originalWeighted_eq_zero_of_coefficient 65 coefficient65

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient67 : L24CorrectionsReplay.fullClaim 67 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted67 : originalWeighted 67 = 0 :=
  originalWeighted_eq_zero_of_coefficient 67 coefficient67

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient68 : L24CorrectionsReplay.fullClaim 68 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted68 : originalWeighted 68 = 0 :=
  originalWeighted_eq_zero_of_coefficient 68 coefficient68

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient71 : L24CorrectionsReplay.fullClaim 71 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted71 : originalWeighted 71 = 0 :=
  originalWeighted_eq_zero_of_coefficient 71 coefficient71

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient72 : L24CorrectionsReplay.fullClaim 72 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted72 : originalWeighted 72 = 0 :=
  originalWeighted_eq_zero_of_coefficient 72 coefficient72

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient73 : L24CorrectionsReplay.fullClaim 73 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted73 : originalWeighted 73 = 0 :=
  originalWeighted_eq_zero_of_coefficient 73 coefficient73

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient75 : L24CorrectionsReplay.fullClaim 75 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted75 : originalWeighted 75 = 0 :=
  originalWeighted_eq_zero_of_coefficient 75 coefficient75

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient77 : L24CorrectionsReplay.fullClaim 77 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted77 : originalWeighted 77 = 0 :=
  originalWeighted_eq_zero_of_coefficient 77 coefficient77

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient78 : L24CorrectionsReplay.fullClaim 78 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted78 : originalWeighted 78 = 0 :=
  originalWeighted_eq_zero_of_coefficient 78 coefficient78

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient79 : L24CorrectionsReplay.fullClaim 79 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted79 : originalWeighted 79 = 0 :=
  originalWeighted_eq_zero_of_coefficient 79 coefficient79

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient80 : L24CorrectionsReplay.fullClaim 80 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted80 : originalWeighted 80 = 0 :=
  originalWeighted_eq_zero_of_coefficient 80 coefficient80

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient82 : L24CorrectionsReplay.fullClaim 82 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted82 : originalWeighted 82 = 0 :=
  originalWeighted_eq_zero_of_coefficient 82 coefficient82

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient84 : L24CorrectionsReplay.fullClaim 84 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted84 : originalWeighted 84 = 0 :=
  originalWeighted_eq_zero_of_coefficient 84 coefficient84

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient85 : L24CorrectionsReplay.fullClaim 85 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted85 : originalWeighted 85 = 0 :=
  originalWeighted_eq_zero_of_coefficient 85 coefficient85

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient86 : L24CorrectionsReplay.fullClaim 86 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted86 : originalWeighted 86 = 0 :=
  originalWeighted_eq_zero_of_coefficient 86 coefficient86

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient87 : L24CorrectionsReplay.fullClaim 87 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted87 : originalWeighted 87 = 0 :=
  originalWeighted_eq_zero_of_coefficient 87 coefficient87

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient89 : L24CorrectionsReplay.fullClaim 89 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted89 : originalWeighted 89 = 0 :=
  originalWeighted_eq_zero_of_coefficient 89 coefficient89

/-- Exact vanishing of the original relation coordinate. -/
theorem coefficient90 : L24CorrectionsReplay.fullClaim 90 = 0 := by
  decide +kernel

/-- The original weighted row vanishes by its original coordinate. -/
theorem weighted90 : originalWeighted 90 = 0 :=
  originalWeighted_eq_zero_of_coefficient 90 coefficient90

end AxiomaticGW.BlowupF1RootZeroRows.CoefficientBatch02
