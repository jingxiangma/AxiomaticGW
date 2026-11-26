/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRootParts

/-!
# Vanishing of a separating root slot from its left component

The existing evaluator checks the right child first. This equality allows a
proved zero on the left to discharge the whole slot without evaluating that
right child. All curves, ordered node states, cotangent decorations, point
distributions, metric signs and binomial coefficients are retained.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- A known zero left contraction annihilates the unchanged separating root slot. -/
theorem scalarPointRootSeparating_eq_zero_of_left (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g₁ (Option S)) (y : GluingExpression g₂ (Option T))
    (dx : x.CotangentDecoration) (dy : y.CotangentDecoration)
    (lx : x.DecidableLabels) (ly : y.DecidableLabels)
    (n : ℕ) (split : X.Curve × X.Curve) (b : SurfaceBasisLabel X)
    (ij : ℕ × ℕ) (a : S ⊕ T → SurfaceBasisLabel X)
    (hx : x.scalarPointContraction X vertex dx lx split.1 ij.1
      (Option.elim · b (a ∘ Sum.inl)) = 0) :
    (x.separating y).scalarPointRootSeparating X vertex (dx, dy) (lx, ly)
      n split b ij a = 0 := by
  simp only [scalarPointRootSeparating, hx, zero_mul, ite_self, mul_zero]

end AxiomaticGW.GluingExpression
