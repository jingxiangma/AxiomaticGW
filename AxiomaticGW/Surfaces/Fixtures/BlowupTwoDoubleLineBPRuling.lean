/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineBPPoint
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineBPLower
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.BPValues

/-! # Two remaining ruling states in the canonical point value at twice the strict line

The original unshifted ruling equations identify its point and far-exceptional values with
its hyperplane value and eliminate the along-axis exceptional value. Each scalar coefficient
below retains the full signed L24 source of the original twice-strict-line equation.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineBP.Shifted
open SurfaceGenusTwoBlowupScalar

/-- The direct twice-line calculation needs only the H and N values on the ruling E₁+L. -/
theorem point_eq_ruling :
    actual (BlowupTwoDoubleLine.curve, .point) =
      ((∑ k ∈ ShiftedLower.remaining, ShiftedLower.weighted k) - coefficient 0 / 960 -
        (coefficient 1 + coefficient 2) / 2880 +
        (coefficient 3 + coefficient 4 + coefficient 7) * actual (ruling, .hyperplane) +
        coefficient 5 * actual (ruling, .primary)) / 2 := by
  have h := BlowupTwoRuling.BP.dependencies 0
  have hr : BlowupTwoRuling.curve 0 = ruling := by decide +kernel
  rw [hr] at h
  change actual (ruling, .point) = actual (ruling, .hyperplane) ∧
    actual (ruling, .exceptional 0) = 0 ∧
    actual (ruling, .exceptional 1) = actual (ruling, .point) at h
  rw [← ShiftedLower.constant_eq_remaining, point_eq_half_hyperplane, value_eq, h.2.1, h.2.2, h.1,
    mul_zero, add_zero]
  ring

end AxiomaticGW.BlowupTwoDoubleLineBP.Shifted
