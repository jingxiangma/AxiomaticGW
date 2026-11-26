/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabel
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootIndex0122

/-!
# Numerical consumers of the accepted row-122 value

These two original weighted values follow from the unchanged row-122 theorem
and the exact relabelling coefficient ratios. No component value is evaluated
and no coincidence in a sampled numerical table is used as a hypothesis.
-/

@[expose] public section

namespace AxiomaticGWTest.BlowupF1RootRelabelNumerical

open AxiomaticGW BlowupF1RootAssembly BlowupF1RootRelabel

/-- Transfer the accepted original row, retaining the coefficient of row 141. -/
theorem originalWeighted141 : originalWeighted 141 = (3527 / 758160 : ℚ) := by
  rw [originalWeighted141_eq_ratio122,
    BlowupF1FullRootReplay.Index0122.original_eq_claimed,
    BlowupF1FullRootReplay.Index0122.claimed]
  norm_num

/-- Row 156 is a separate original occurrence with the same exact transferred value. -/
theorem originalWeighted156 : originalWeighted 156 = (3527 / 758160 : ℚ) := by
  rw [originalWeighted156_eq_ratio122,
    BlowupF1FullRootReplay.Index0122.original_eq_claimed,
    BlowupF1FullRootReplay.Index0122.claimed]
  norm_num

end AxiomaticGWTest.BlowupF1RootRelabelNumerical
