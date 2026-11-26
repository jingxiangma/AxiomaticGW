/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointContraction

/-!
# External assignment congruence for scalar point contractions

An outer relabelling only transports the external states. Equal transported
assignments therefore give the same contraction for arbitrary component data,
without requiring vertex equivariance or evaluating a component backend.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

/-- Equal transported external states preserve the unchanged full contraction. -/
theorem scalarPointContraction_relabel_eq_of_labels (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (e f : S ≃ T) (beta : X.Curve) (n : ℕ) (a : T → SurfaceBasisLabel X)
    (ha : a ∘ e = a ∘ f) :
    (x.relabel e).scalarPointContraction X vertex d l beta n a =
      (x.relabel f).scalarPointContraction X vertex d l beta n a := by
  change x.scalarPointContraction X vertex d l beta n (a ∘ e) =
    x.scalarPointContraction X vertex d l beta n (a ∘ f)
  rw [ha]

end AxiomaticGW.GluingExpression
