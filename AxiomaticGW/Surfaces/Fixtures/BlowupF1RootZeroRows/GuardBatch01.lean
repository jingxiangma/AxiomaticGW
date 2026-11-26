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

namespace AxiomaticGW.BlowupF1RootZeroRows.GuardBatch01

open BlowupF1RootAssembly

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient119_nonzero : L24CorrectionsReplay.fullClaim 119 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard119 : 2 ≤ (L24Gluing.term 119).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted119 : originalWeighted 119 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 119 genusGuard119

/-- This original coordinate is not included among the zero-coordinate rows. -/
theorem coefficient120_nonzero : L24CorrectionsReplay.fullClaim 120 ≠ 0 := by
  decide +kernel

/-- The actual source expression is removed by the existing genus guard. -/
theorem genusGuard120 : 2 ≤ (L24Gluing.term 120).expression.maxComponentGenus := by
  decide +kernel

/-- This is the guarded weighted row; no unguarded vanishing is asserted. -/
theorem weighted120 : originalWeighted 120 = 0 :=
  originalWeighted_eq_zero_of_genus_guard 120 genusGuard120

end AxiomaticGW.BlowupF1RootZeroRows.GuardBatch01
