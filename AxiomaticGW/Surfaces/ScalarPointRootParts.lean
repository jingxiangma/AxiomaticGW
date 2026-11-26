/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointContraction

/-!
# Root summands of the existing scalar point contraction

These three projections expose only the first gluing operation, passing through
external relabellings. Child contractions and their signed point pullbacks remain
the existing evaluator. A separating root has one summand for each full curve
split, basis state and ordered point distribution; a nonseparating root has one
summand per basis state. The fundamental projection retains its actual vertex.

The sum theorem reconstructs the existing contraction for arbitrary vertex data.
No graph representation, cache key, geometric law or numerical seed is added.
-/

@[expose] public section

namespace AxiomaticGW.GluingExpression

open scoped BigOperators

/-- The vertex contribution when the root, after relabelling, is fundamental. -/
def scalarPointRootFundamental (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      X.Curve → ℕ → (S → SurfaceBasisLabel X) → ℚ
  | @fundamental g S _ h, d, l, beta, n, a => vertex n g S h d l beta a
  | @relabel _ _ _ _ _ e x, d, l, beta, n, a =>
      x.scalarPointRootFundamental X vertex d l beta n (a ∘ e)
  | @separating _ _ _ _ _ _ _ _, _, _, _, _, _ => 0
  | @nonseparating _ _ _ _, _, _, _, _, _ => 0

/-- One separating-root summand with the original signed inverse metric,
binomial count, ordered node labels and unchanged child contractions. -/
def scalarPointRootSeparating (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      ℕ → (X.Curve × X.Curve) → SurfaceBasisLabel X → (ℕ × ℕ) →
      (S → SurfaceBasisLabel X) → ℚ
  | @fundamental _ _ _ _, _, _, _, _, _, _, _ => 0
  | @relabel _ _ _ _ _ e x, d, l, n, split, b, ij, a =>
      x.scalarPointRootSeparating X vertex d l n split b ij (a ∘ e)
  | @separating _ _ _ _ _ _ x y, d, l, n, split, b, ij, a =>
      b.inverseWeight * ((n.choose ij.1 : ℚ) *
        (let right := y.scalarPointContraction X vertex d.2 l.2 split.2 ij.2
          (Option.elim · b.dual (a ∘ Sum.inr))
         if right = 0 then 0 else
           x.scalarPointContraction X vertex d.1 l.1 split.1 ij.1
             (Option.elim · b (a ∘ Sum.inl)) * right))
  | @nonseparating _ _ _ _, _, _, _, _, _, _, _ => 0

/-- One nonseparating-root summand; the complete curve and point count remain
on the child, with both original ordered distinguished node labels. -/
def scalarPointRootNonseparating (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      X.Curve → ℕ → SurfaceBasisLabel X → (S → SurfaceBasisLabel X) → ℚ
  | @fundamental _ _ _ _, _, _, _, _, _, _ => 0
  | @relabel _ _ _ _ _ e x, d, l, beta, n, b, a =>
      x.scalarPointRootNonseparating X vertex d l beta n b (a ∘ e)
  | @separating _ _ _ _ _ _ _ _, _, _, _, _, _, _ => 0
  | @nonseparating _ _ _ x, d, l, beta, n, b, a =>
      b.inverseWeight * x.scalarPointContraction X vertex d l beta n
        (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Exact decomposition at the first gluing operation, including all zero slots. -/
theorem scalarPointContraction_eq_root_parts (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    x.scalarPointContraction X vertex d l beta n a =
      x.scalarPointRootFundamental X vertex d l beta n a +
      (∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          x.scalarPointRootSeparating X vertex d l n split b ij a) +
      ∑ b : SurfaceBasisLabel X,
        x.scalarPointRootNonseparating X vertex d l beta n b a := by
  induction x generalizing beta n with
  | fundamental g S h =>
    simp only [scalarPointContraction, scalarPointRootFundamental,
      scalarPointRootSeparating, scalarPointRootNonseparating,
      Finset.sum_const_zero, add_zero]
  | relabel e x ih => exact ih d l beta n (a ∘ e)
  | separating x y _ _ =>
    simp only [scalarPointContraction, scalarPointRootFundamental,
      scalarPointRootSeparating, scalarPointRootNonseparating,
      Finset.sum_const_zero, Finset.mul_sum, zero_add, add_zero]
  | nonseparating x _ =>
    simp only [scalarPointContraction, scalarPointRootFundamental,
      scalarPointRootSeparating, scalarPointRootNonseparating,
      Finset.sum_const_zero, zero_add]

/-- Preserve an arbitrary original relation coefficient on every root summand. -/
theorem weighted_scalarPointContraction_eq_root_parts (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) (c : ℚ) :
    c * x.scalarPointContraction X vertex d l beta n a =
      c * x.scalarPointRootFundamental X vertex d l beta n a +
      (∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          c * x.scalarPointRootSeparating X vertex d l n split b ij a) +
      ∑ b : SurfaceBasisLabel X,
        c * x.scalarPointRootNonseparating X vertex d l beta n b a := by
  rw [scalarPointContraction_eq_root_parts]
  simp only [mul_add, Finset.mul_sum]

end AxiomaticGW.GluingExpression
