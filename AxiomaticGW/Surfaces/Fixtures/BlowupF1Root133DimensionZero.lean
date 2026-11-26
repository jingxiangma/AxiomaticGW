/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRootZero
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Actual left dimension zero for original F1 row133

At the original split0/unit/point0 slot, expression53 has a genus-one left
component in class(0,0), no added point, zero cotangent powers, and E0/unit
insertions. Its total codimension1 differs from virtualdimension2. The existing
generic zero theorem preserves the full right subtree and original coefficients.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1Root133DimensionZero
open SurfaceGenusTwo BlowupF1RootAssembly

/-- The original zero slot is certified for every existing residual cache. -/
theorem separating133_split0_unit_point0 (cache : ResidualCache X) :
    separatingPart cache 133 0 .unit 0 = 0 := by
  change L24CorrectionsReplay.fullClaim 133 *
    L24Gluing.term133.expression.scalarPointRootSeparating X (vertex cache)
      L24Gluing.term133.decoration L24Gluing.term133.labels 1
      (sourceSplits 0) .unit (0, 1) insertions = 0
  simp only [L24Gluing.term133, L24Gluing.expression53, GetzlerGraphs.join]
  apply mul_eq_zero_of_right
  apply GluingExpression.scalarPointRootSeparating_eq_zero_of_left
  simp only [GluingExpression.scalarPointContraction, vertex,
    SurfacePointPullback.vertex, constantVertexWithPointLookup, Nat.le_refl, if_true]
  apply if_neg
  decide +kernel

end AxiomaticGW.BlowupF1Root133DimensionZero
