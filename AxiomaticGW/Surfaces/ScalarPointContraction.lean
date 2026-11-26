/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PointPullbackContraction

/-!
# Scalar point contraction with zero-product pruning

This evaluator has exactly the existing graph, class and marking sums.
At a separating edge a zero right factor avoids evaluating the left factor.
In the fixed BP graphs the right factor is often a single primary component.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

private theorem mulSkipRight (l r : ℚ) : (if r = 0 then 0 else l * r) = l * r := by
  by_cases hr : r = 0
  · rw [if_pos hr, hr, mul_zero]
  · exact if_neg hr

/-- The scalar form preserves every split and binomial coefficient. -/
def scalarPointContraction (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      X.Curve → ℕ → (S → SurfaceBasisLabel X) → ℚ
  | @fundamental g S _ h, d, l, beta, n, a => vertex n g S h d l beta a
  | @relabel _ _ _ _ _ e x, d, l, beta, n, a =>
      x.scalarPointContraction X vertex d l beta n (a ∘ e)
  | @separating _ _ _ _ _ _ x y, d, l, beta, n, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        b.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (n.choose ij.1 : ℚ) *
            (let right := y.scalarPointContraction X vertex d.2 l.2 split.2 ij.2
                (Option.elim · b.dual (a ∘ Sum.inr))
             if right = 0 then 0 else
               x.scalarPointContraction X vertex d.1 l.1 split.1 ij.1
                 (Option.elim · b (a ∘ Sum.inl)) * right)
  | @nonseparating _ _ _ x, d, l, beta, n, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        x.scalarPointContraction X vertex d l beta n
          (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Zero pruning is an exact implementation of the original contraction. -/
theorem scalarPointContraction_eq (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    x.scalarPointContraction X vertex d l beta n a =
      x.pointContraction X vertex d l beta n a := by
  induction x generalizing beta n with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih d l beta n (a ∘ e)
  | separating x y ihx ihy =>
    simp only [scalarPointContraction, pointContraction, mulSkipRight, ihx, ihy,
      Algebra.algebraMap_self_apply]
  | nonseparating x ih =>
    simp only [scalarPointContraction, pointContraction, ih, Algebra.algebraMap_self_apply]

end AxiomaticGW.GluingExpression
