/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoNormalizedL24
public import AxiomaticGW.Surfaces.Fixtures.L24

/-!
# Normalization of the complete degree-zero L24 equation

The 815-column certificate gives the residual genus-two dilaton equation.
The existing primary/first-descendant normalization makes that equation
identically zero. This checks normalization without supplying a new invariant.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoNormalizedL24
open SurfacePolynomialReduction L24Relation

set_option maxRecDepth 20000

/-- The complete degree-zero residual is the already known dilaton identity. -/
theorem planeZero_normalized : RationalTerms.Equivalent
    (RationalTerms.affineSubstitute normalizedTerms SurfaceL24.planeZero) 0 := by
  decide +kernel

/-- Bind the normalized identity to all original L24 columns under any valuation. -/
theorem eval_planeZero (v : Variable .plane → ℚ) :
    RationalTerms.eval v (normalizedGenusTwoTerms .plane 0 0 0
      ![.hyperplane, .hyperplane, .unit, .unit]) = 0 := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute_eq_of_equivalent v
    normalizedTerms _ _ SurfaceL24.planeZero_checked
    (genusTwoTerms_card_le_one _ _ _ _ _) (by decide +kernel)]
  rw [RationalTerms.eval_eq_of_equivalent v _ _ planeZero_normalized,
    RationalTerms.eval_zero]

end AxiomaticGW.SurfaceGenusTwoNormalizedL24
