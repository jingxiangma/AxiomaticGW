/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.CurveSum
public import AxiomaticGW.Surfaces.GenusTwoRemainder

/-!
# Scalar contractions without extra point markings

The only point distribution is (0,0). Enumerating the first curve class
in effective coordinates determines the complementary class by subtraction.
For a singleton coefficient, the genus-two factor is evaluated before the
rational complement, so a vanishing coefficient skips that complement.
-/

@[expose] public section
namespace AxiomaticGW

private theorem skip_right (a b : ℚ) : (if b = 0 then 0 else a * b) = a * b := by
  split_ifs with h
  · rw [h, mul_zero]
  · rfl

private theorem skip_left (a b : ℚ) : (if a = 0 then 0 else a * b) = a * b := by
  split_ifs with h
  · rw [h, zero_mul]
  · rfl

namespace GluingExpression

/-- Exact scalar evaluation of a decorated graph at point budget zero. -/
def zeroPointContraction (X : SurfaceTarget) (vertex : SurfaceCotangentVertexValues X ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
      x.CotangentDecoration → x.DecidableLabels → X.Curve → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @fundamental g S _ h, d, l, beta, a => vertex g S h d l beta a
  | _, _, _, @relabel _ _ _ _ _ e x, d, l, beta, a =>
    zeroPointContraction X vertex x d l beta (a ∘ e)
  | _, _, _, @separating _ _ _ _ _ _ x y, d, l, beta, a =>
    X.sumSubcurves beta fun c ↦ ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      (let right := zeroPointContraction X vertex y d.2 l.2 (beta - c)
         (Option.elim · b.dual (a ∘ Sum.inr))
       if right = 0 then 0 else
         zeroPointContraction X vertex x d.1 l.1 c (Option.elim · b (a ∘ Sum.inl)) * right)
  | _, _, _, @nonseparating _ _ _ x, d, l, beta, a =>
    ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      zeroPointContraction X vertex x d l beta (Option.elim · b (fun t ↦ Option.elim t b.dual a))

theorem zeroPointContraction_eq (X : SurfaceTarget) (vertex : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (d : x.CotangentDecoration)
    (l : x.DecidableLabels) (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    zeroPointContraction X (vertex 0) x d l beta a = x.pointContraction X vertex d l beta 0 a := by
  induction x generalizing beta with
  | fundamental => rfl
  | relabel e x ih => exact ih d l beta (a ∘ e)
  | separating x y ihx ihy =>
    simp only [zeroPointContraction, pointContraction, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one, one_mul, skip_right,
      ihx, ihy, Algebra.algebraMap_self_apply]
    rw [SurfaceTarget.sumSubcurves_eq, SurfaceTarget.splittings, WeightedCurveClass.splittings,
      Finset.sum_image (fun _ _ _ _ h ↦ congrArg Prod.fst h)]
  | nonseparating x ih => simp only [zeroPointContraction, pointContraction, ih,
      Algebra.algebraMap_self_apply]

end GluingExpression

namespace SurfaceGenusTwo
open SurfacePolynomialReduction

/-- Evaluate the singleton coefficient with zero extra points and an effective remainder. -/
def zeroPointRemainder (X : SurfaceTarget) (v : Variable X)
    (main : SurfaceCotangentVertexValues X ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
      x.CotangentDecoration → x.DecidableLabels → X.Curve → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, d, l, delta, a =>
    if g = 2 then main g S h d l delta a else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, d, l, delta, a =>
    zeroPointRemainder X v main x d l delta (a ∘ e)
  | _, _, _, @GluingExpression.separating g h _ _ _ _ x y, d, l, delta, a =>
    if g = 2 then X.sumSubcurves delta fun c ↦ ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      (let left := zeroPointRemainder X v main x d.1 l.1 c (Option.elim · b (a ∘ Sum.inl))
       if left = 0 then 0 else left *
         y.zeroPointContraction X (primaryPointVertex X v 0) d.2 l.2 (delta - c)
           (Option.elim · b.dual (a ∘ Sum.inr)))
    else if h = 2 then X.sumSubcurves delta fun c ↦ ∑ b : SurfaceBasisLabel X, b.inverseWeight *
      (let right := zeroPointRemainder X v main y d.2 l.2 (delta - c)
         (Option.elim · b.dual (a ∘ Sum.inr))
       if right = 0 then 0 else
         x.zeroPointContraction X (primaryPointVertex X v 0) d.1 l.1 c
           (Option.elim · b (a ∘ Sum.inl)) * right)
    else 0
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _, _, _ => 0

theorem zeroPointRemainder_eq (X : SurfaceTarget) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : X.Curve) (a : S → SurfaceBasisLabel X) :
    zeroPointRemainder X v (main 0) x d l delta a =
      remainderContraction X v main x d l delta 0 a := by
  induction x generalizing delta with
  | fundamental => rfl
  | relabel e x ih => exact ih d l delta (a ∘ e)
  | @separating g h _ _ _ _ x y ihx ihy =>
    simp only [zeroPointRemainder, remainderContraction, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one, one_mul, skip_right, skip_left,
      ihx, ihy, GluingExpression.zeroPointContraction_eq]
    split_ifs <;> first | rfl | rw [SurfaceTarget.sumSubcurves_eq, SurfaceTarget.splittings,
      WeightedCurveClass.splittings, Finset.sum_image (fun _ _ _ _ he ↦ congrArg Prod.fst he)]
  | nonseparating => rfl

end SurfaceGenusTwo
end AxiomaticGW
