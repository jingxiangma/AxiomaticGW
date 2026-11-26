/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DecoratedGluingEvaluation
public import AxiomaticGW.Surfaces.GenusZeroMarkings
public import AxiomaticGW.Tautological.DecoratedGluingMarking
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial contraction of signed point pullbacks

Additional labelled primary points are counted at each separating edge instead
of enumerating all graph placements. Cotangent pullbacks at a single component
still use the original positive term and negative rational-tail corrections.
The component computation decreases the number of new points, including when
a correction increases the graph size. No relation or invariant is assumed.
-/

@[expose] public section

namespace AxiomaticGW

/-- Component values with explicit label decisions for cotangent pullback. -/
abbrev SurfaceCotangentVertexValues (X : SurfaceTarget) (A : Type*) :=
  ∀ (g : ℕ) (S : Type) [Fintype S], StableArity g S → (S → ℕ) →
    DecidableEq S → X.Curve → (S → SurfaceBasisLabel X) → A

namespace GluingExpression

/-- Distribute point counts binomially through the original graph. The supplied
component family includes all signed pullbacks internal to that component. -/
def pointContraction {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (vertex : ℕ → SurfaceCotangentVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] :
    (x : GluingExpression g S) → x.CotangentDecoration → x.DecidableLabels →
      X.Curve → ℕ → (S → SurfaceBasisLabel X) → A
  | @fundamental g S _ h, d, l, beta, n, a => vertex n g S h d l beta a
  | @relabel _ _ _ _ _ e x, d, l, beta, n, a =>
      x.pointContraction X vertex d l beta n (a ∘ e)
  | @separating _ _ _ _ _ _ x y, d, l, beta, n, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        algebraMap ℚ A b.inverseWeight *
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : A) *
            (x.pointContraction X vertex d.1 l.1 split.1 ij.1
                (Option.elim · b (a ∘ Sum.inl)) *
             y.pointContraction X vertex d.2 l.2 split.2 ij.2
                (Option.elim · b.dual (a ∘ Sum.inr)))
  | @nonseparating _ _ _ x, d, l, beta, n, a =>
      ∑ b : SurfaceBasisLabel X, algebraMap ℚ A b.inverseWeight *
        x.pointContraction X vertex d l beta n
          (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Only component values at point counts no larger than the request are used. -/
theorem pointContraction_congr {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (v w : ℕ → SurfaceCotangentVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve)
    (n : ℕ) (a : S → SurfaceBasisLabel X) (hv : ∀ m, m ≤ n → v m = w m) :
    x.pointContraction X v d l beta n a = x.pointContraction X w d l beta n a := by
  induction x generalizing n beta with
  | fundamental g S h => rw [pointContraction, pointContraction, hv n le_rfl]
  | relabel e x ih => exact ih d l beta n (a ∘ e) hv
  | separating x y ihx ihy =>
    simp only [pointContraction]
    apply Finset.sum_congr rfl
    intro split _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [ihx d.1 l.1 split.1 ij.1 _ (fun m hm ↦ hv m (by omega)),
      ihy d.2 l.2 split.2 ij.2 _ (fun m hm ↦ hv m (by omega))]
  | nonseparating x ih =>
    simp only [pointContraction]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih d l beta n _ hv]

end GluingExpression

namespace SurfacePointPullback

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The original signed universal-curve formula, computed with compressed graph
contractions. Recursion decreases the number of additional point markings. -/
def vertex (X : SurfaceTarget) (value : SurfaceVertexValues X A) (n : ℕ) :
    SurfaceCotangentVertexValues X A :=
  match n with
  | 0 => fun g S _ h d _ beta a ↦ value g S h beta d a
  | n + 1 => fun g S _ h d l beta a ↦
      (((GluingExpression.fundamental g S h).addCotangentMarking d l).map fun t ↦
        (t.1 : A) * t.2.expression.pointContraction X
          (fun m ↦ if _hm : m ≤ n then vertex X value m else fun _ _ _ _ _ _ _ _ ↦ 0)
          t.2.decoration t.2.labels beta n (Option.elim · .point a)).sum
termination_by n
decreasing_by omega

/-- The bound in the terminating definition never changes a used component value. -/
theorem vertex_succ (X : SurfaceTarget) (value : SurfaceVertexValues X A)
    (n g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (d : S → ℕ)
    (l : DecidableEq S) (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    vertex X value (n + 1) g S h d l beta a =
      (((GluingExpression.fundamental g S h).addCotangentMarking d l).map fun t ↦
        (t.1 : A) * t.2.expression.pointContraction X (vertex X value)
          t.2.decoration t.2.labels beta n (Option.elim · .point a)).sum := by
  rw [vertex]
  dsimp only
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro t _
  congr 1
  apply GluingExpression.pointContraction_congr
  intro m hm
  exact dif_pos hm

/-- With no additional points the original decorated contraction is recovered. -/
theorem contraction_zero (X : SurfaceTarget) (value : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve)
    (a : S → SurfaceBasisLabel X) :
    x.pointContraction X (vertex X value) d l beta 0 a =
      x.surfaceDecoratedEval X value d beta 0 a := by
  induction x generalizing beta with
  | fundamental g S h =>
    simp only [GluingExpression.pointContraction, vertex,
      GluingExpression.surfaceDecoratedEval, zero_add]
  | relabel e x ih => exact ih d l beta (a ∘ e)
  | @separating g h S T _ _ x y ihx ihy =>
    have hl : PsiClasses.separatingLeftPowers (0 : S ⊕ T → ℕ) = 0 := by
      funext s; cases s <;> rfl
    have hr : PsiClasses.separatingRightPowers (0 : S ⊕ T → ℕ) = 0 := by
      funext s; cases s <;> rfl
    simp only [GluingExpression.pointContraction, GluingExpression.surfaceDecoratedEval,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Nat.choose_zero_right,
      Nat.cast_one, one_mul, ihx, ihy, hl, hr]
  | @nonseparating g S _ x ih =>
    have hk : PsiClasses.nonseparatingPowers (0 : S → ℕ) = 0 := by
      funext s; rcases s with _ | (_ | s) <;> rfl
    simp only [GluingExpression.pointContraction, GluingExpression.surfaceDecoratedEval, ih, hk]

omit [Algebra ℚ A] in
private theorem binomial_succ (f g : ℕ → A) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (n.choose ij.1 : A) * (f (ij.1 + 1) * g ij.2)) +
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        (n.choose ij.1 : A) * (f ij.1 * g (ij.2 + 1))) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), ((n + 1).choose ij.1 : A) *
          (f ij.1 * g ij.2) := by
  rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j ↦ f i * g j) n, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hsum, Nat.choose_symm_add]

omit [Algebra ℚ A] in
private theorem sum_weighted_mul {α : Type*} (m : Multiset α)
    (w f : α → A) (c : A) :
    (m.map (fun t ↦ w t * (c * f t))).sum =
      c * (m.map (fun t ↦ w t * f t)).sum := by
  rw [← Multiset.sum_map_mul_left]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro t _
  exact mul_left_comm _ _ _

omit [Algebra ℚ A] in
private theorem sum_weighted_mul_right {α : Type*} (m : Multiset α)
    (w f : α → A) (c : A) :
    (m.map (fun t ↦ w t * (f t * c))).sum =
      (m.map (fun t ↦ w t * f t)).sum * c := by
  simp only [← mul_assoc, Multiset.sum_map_mul_right]

/-- Pascal's identity preserves both positive placements and all signed tails. -/
theorem sum_contraction_addMarking (X : SurfaceTarget) (value : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels) (beta : X.Curve)
    (n : ℕ) (a : S → SurfaceBasisLabel X) :
    ((x.addCotangentMarking d l).map fun t ↦ (t.1 : A) *
      t.2.expression.pointContraction X (vertex X value) t.2.decoration t.2.labels
        beta n (Option.elim · .point a)).sum =
      x.pointContraction X (vertex X value) d l beta (n + 1) a := by
  induction x generalizing beta n with
  | fundamental g S h => exact (vertex_succ X value n g S h d l beta a).symm
  | relabel e x ih =>
    have he : (Option.elim · SurfaceBasisLabel.point a) ∘ e.optionCongr =
        (Option.elim · .point (a ∘ e)) := by
      funext t; cases t <;> rfl
    simp only [GluingExpression.addCotangentMarking, Multiset.map_map, Function.comp_def,
      GluingExpression.CotangentTerm.relabel, GluingExpression.pointContraction]
    change ((x.addCotangentMarking d l).map fun t ↦ (t.1 : A) *
      t.2.expression.pointContraction X (vertex X value) t.2.decoration t.2.labels
        beta n ((Option.elim · .point a) ∘ e.optionCongr)).sum = _
    rw [he]
    exact ih d l beta n (a ∘ e)
  | @separating g h S T _ _ x y ihx ihy =>
    have hlx (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivLeft S T).symm) ∘
          Sum.inl)) ∘ swapDoubleOption S =
        (Option.elim · .point (Option.elim · b (a ∘ Sum.inl))) := by
      funext t; rcases t with _ | (_ | s) <;> rfl
    have hly (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivLeft S T).symm) ∘
          Sum.inr)) = (Option.elim · b (a ∘ Sum.inr)) := by
      funext t; cases t <;> rfl
    have hrx (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivRight S T).symm) ∘
          Sum.inl)) = (Option.elim · b (a ∘ Sum.inl)) := by
      funext t; cases t <;> rfl
    have hry (b : SurfaceBasisLabel X) :
        (Option.elim · b (((Option.elim · .point a) ∘ (optionSumEquivRight S T).symm) ∘
          Sum.inr)) ∘ swapDoubleOption T =
        (Option.elim · .point (Option.elim · b (a ∘ Sum.inr))) := by
      funext t; rcases t with _ | (_ | s) <;> rfl
    simp only [GluingExpression.addCotangentMarking, Multiset.map_add, Multiset.sum_add,
      Multiset.map_map, Function.comp_def]
    simp only [GluingExpression.CotangentTerm.relabel,
      GluingExpression.CotangentTerm.separating, GluingExpression.pointContraction,
      hlx, hly, hrx, hry]
    simp only [Finset.mul_sum, Multiset.sum_map_sum]
    simp only [sum_weighted_mul, sum_weighted_mul_right, ihx, ihy]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro split _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← Finset.mul_sum]
    congr 1
    exact binomial_succ
      (fun k ↦ x.pointContraction X (vertex X value) d.1 l.1 split.1 k
        (Option.elim · b (a ∘ Sum.inl)))
      (fun k ↦ y.pointContraction X (vertex X value) d.2 l.2 split.2 k
        (Option.elim · b.dual (a ∘ Sum.inr))) n
  | @nonseparating g S _ x ih =>
    have he (b : SurfaceBasisLabel X) :
        (Option.elim · b (fun t ↦ Option.elim t b.dual (Option.elim · .point a))) ∘
          (forgetNonseparatingEquiv S).symm =
        (Option.elim · .point (Option.elim · b (fun t ↦ Option.elim t b.dual a))) := by
      funext t; rcases t with _ | (_ | (_ | s)) <;> rfl
    simp only [GluingExpression.addCotangentMarking, Multiset.map_map, Function.comp_def]
    simp only [GluingExpression.CotangentTerm.nonseparating, GluingExpression.CotangentTerm.relabel,
      GluingExpression.pointContraction, he, Finset.mul_sum, Multiset.sum_map_sum,
      sum_weighted_mul, ih]

/-- Iteration preserves each integer coefficient and its repeated placements. -/
theorem sum_contraction_addMarkings (X : SurfaceTarget) (value : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (beta : X.Curve) (n m : ℕ) (a : S → SurfaceBasisLabel X) :
    ((z.addMarkings n).map fun t ↦ (t.1 : A) *
      t.2.expression.pointContraction X (vertex X value) t.2.decoration t.2.labels
        beta m (SurfaceGenusZero.pointLabels a n)).sum =
      z.expression.pointContraction X (vertex X value) z.decoration z.labels beta (m + n) a := by
  induction n generalizing m with
  | zero =>
    simp only [GluingExpression.CotangentTerm.addMarkings, SurfaceGenusZero.pointLabels,
      Multiset.map_singleton, Multiset.sum_singleton, Int.cast_one, one_mul, Nat.add_zero]
  | succ n ih =>
    rw [GluingExpression.CotangentTerm.addMarkings, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_map, Function.comp_def, Int.cast_mul, mul_assoc,
      Multiset.sum_map_mul_left, GluingExpression.CotangentTerm.addMarking,
      SurfaceGenusZero.pointLabels, sum_contraction_addMarking]
    rw [ih]
    rw [show m + 1 + n = m + (n + 1) by omega]

/-- Uniform equality with the complete signed decorated pullback, for any
terminal component values and every number of additional primary points. -/
theorem contraction_eq (X : SurfaceTarget) (value : SurfaceVertexValues X A)
    {g : ℕ} {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    z.expression.pointContraction X (vertex X value) z.decoration z.labels beta n a =
      ((z.addMarkings n).map fun t ↦ (t.1 : A) *
        t.2.expression.surfaceDecoratedEval X value t.2.decoration beta 0
          (SurfaceGenusZero.pointLabels a n)).sum := by
  simpa only [contraction_zero, zero_add] using
    (sum_contraction_addMarkings X value z beta n 0 a).symm

end SurfacePointPullback
end AxiomaticGW
