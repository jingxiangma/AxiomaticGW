/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootAssembly

/-!
# Dimension-selected zero at one original F1 root slot

The original term122 shares expression51 with term121. At split0, node state
unit and point distribution (0,1), its left elliptic component has degree zero,
one unit insertion and no cotangent power. Its dimension guard is false.
This proof uses that component before evaluating the right subtree; the existing
right-first evaluator and all original coefficients remain unchanged.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1RootDimensionZero
open SurfaceGenusTwo BlowupF1RootAssembly
open BlowupF1CertifiedPoints (rational elliptic)

private theorem skippedProduct_zero_of_left (l r : ℚ) (hl : l = 0) :
    (if r = 0 then 0 else l * r) = 0 := by
  rw [hl, zero_mul, ite_self]

/-- The actual original slot vanishes for every existing certified cache. -/
theorem separating122_split0_unit_point0 (cache : ResidualCache X) :
    separatingPart cache 122 0 .unit 0 = 0 := by
  change L24CorrectionsReplay.fullClaim 122 *
    L24Gluing.term122.expression.scalarPointRootSeparating X (vertex cache)
      L24Gluing.term122.decoration L24Gluing.term122.labels 1
      (sourceSplits 0) .unit (0, 1) insertions = 0
  simp only [L24Gluing.term122, L24Gluing.expression51, GetzlerGraphs.join,
    GluingExpression.scalarPointRootSeparating]
  rw [skippedProduct_zero_of_left _ _ ?_]
  · simp only [mul_zero]
  · simp only [GluingExpression.scalarPointContraction, vertex,
      SurfacePointPullback.vertex, constantVertexWithPointLookup, Nat.le_refl, if_true]
    apply if_neg
    decide +kernel

end AxiomaticGW.BlowupF1RootDimensionZero
