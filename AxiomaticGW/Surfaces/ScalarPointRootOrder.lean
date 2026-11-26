/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.ScalarPointRootParts

/-!
# Left-first evaluation of a separating root summand

Some L24 roots have a simple left vertex and a large right subtree. The
existing right-first short circuit evaluates that subtree even when the left
vertex vanishes. This alternative checks the left factor first and is proved
equal to the existing root summand for arbitrary component data. Child
contractions, ordered node states, curve splits and point allocations are
unchanged. The original evaluator and all accepted certificates are retained.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GluingExpression

private theorem mulSkipRight_eq_mulSkipLeft (left right : ℚ) :
    (if right = 0 then 0 else left * right) =
      (if left = 0 then 0 else left * right) := by
  by_cases hl : left = 0
  · simp only [hl, zero_mul, ite_self]
  · by_cases hr : right = 0
    · simp only [hr, mul_zero, ite_self]
    · rw [if_neg hr, if_neg hl]

/-- Evaluate the same root summand, checking its left child for zero first. -/
def scalarPointRootSeparatingLeftFirst (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      ℕ → (X.Curve × X.Curve) → SurfaceBasisLabel X → (ℕ × ℕ) →
      (S → SurfaceBasisLabel X) → ℚ
  | @fundamental _ _ _ _, _, _, _, _, _, _, _ => 0
  | @relabel _ _ _ _ _ e x, d, l, n, split, b, ij, a =>
      x.scalarPointRootSeparatingLeftFirst X vertex d l n split b ij (a ∘ e)
  | @separating _ _ _ _ _ _ x y, d, l, n, split, b, ij, a =>
      b.inverseWeight * ((n.choose ij.1 : ℚ) *
        (let left := x.scalarPointContraction X vertex d.1 l.1 split.1 ij.1
          (Option.elim · b (a ∘ Sum.inl))
         if left = 0 then 0 else
           left * y.scalarPointContraction X vertex d.2 l.2 split.2 ij.2
             (Option.elim · b.dual (a ∘ Sum.inr))))
  | @nonseparating _ _ _ _, _, _, _, _, _, _, _ => 0

/-- Changing only the short-circuit order preserves the full root summand. -/
theorem scalarPointRootSeparating_eq_leftFirst (X : SurfaceTarget)
    (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (n : ℕ)
    (split : X.Curve × X.Curve) (b : SurfaceBasisLabel X) (ij : ℕ × ℕ)
    (a : S → SurfaceBasisLabel X) :
    x.scalarPointRootSeparating X vertex d l n split b ij a =
      x.scalarPointRootSeparatingLeftFirst X vertex d l n split b ij a := by
  induction x with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih d l (a ∘ e)
  | separating x y _ _ =>
    simp only [scalarPointRootSeparating, scalarPointRootSeparatingLeftFirst,
      mulSkipRight_eq_mulSkipLeft]
  | nonseparating x _ => rfl

end AxiomaticGW.GluingExpression
