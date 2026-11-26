/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineCanonicalComparison
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineL24.Assembly

/-! # The absolute five-row GKM comparison on the strict transform of the line -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoLineCanonical
open SurfaceGenusTwoBlowupOrder

/-- All five ordinary specializations agree with their reconstructed canonical values. -/
theorem accepted (i : Fin 5) :
    canonicalValuation (SurfaceGenusTwoBlowupRecursion.values 0) (.inr (requests i)) =
      values i := by
  apply sub_eq_zero.mp
  rw [discrepancy, ← BlowupTwoLineH.constant_eq_sum, BlowupTwoLineH.constant_value, sub_self]

end AxiomaticGW.GKM.BlowupTwoLineCanonical
