/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRootZero
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# The actual zero left component of original F1 row124

At split0 with unit node and point allocation(0,1), expression51 has a genus-one
left component in class(0,0), one unit insertion and no cotangent power. The
existing dimension guard is false. The right subtree, including its distinct
row124 cotangent decoration, remains unchanged and need not be evaluated.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1Root124DimensionZero
open SurfaceGenusTwo BlowupF1RootAssembly

/-- The original zero slot is certified for every existing residual cache. -/
theorem separating124_split0_unit_point0 (cache : ResidualCache X) :
    separatingPart cache 124 0 .unit 0 = 0 := by
  change L24CorrectionsReplay.fullClaim 124 *
    L24Gluing.term124.expression.scalarPointRootSeparating X (vertex cache)
      L24Gluing.term124.decoration L24Gluing.term124.labels 1
      (sourceSplits 0) .unit (0, 1) insertions = 0
  simp only [L24Gluing.term124, L24Gluing.expression51, GetzlerGraphs.join]
  apply mul_eq_zero_of_right
  apply GluingExpression.scalarPointRootSeparating_eq_zero_of_left
  simp only [GluingExpression.scalarPointContraction, vertex,
    SurfacePointPullback.vertex, constantVertexWithPointLookup, Nat.le_refl, if_true]
  apply if_neg
  decide +kernel

end AxiomaticGW.BlowupF1Root124DimensionZero
