/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.WeightedCurveSplitting
public import AxiomaticGW.Surfaces.GenusTwoCoefficientSupport
public import AxiomaticGW.Surfaces.GenusTwoPrimaryPoints

/-!
# Genus-two contraction over an effective remainder

Fix the full class of the requested genus-two coefficient and distribute only
the effective remainder through the rational complements. Additional points
retain their binomial multiplicities. The terminal genus-two family is an
explicit parameter, so the same contraction handles signed cotangent tails.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

/-- The main component receives its remaining effective class; rational
components receive their actual class. Only a genus-two branch is followed. -/
def remainderContraction (X : SurfaceTarget) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
      x.CotangentDecoration → x.DecidableLabels → X.Curve → ℕ →
        (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, d, l, delta, n, a =>
      if g = 2 then main n g S h d l delta a else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, d, l, delta, n, a =>
      remainderContraction X v main x d l delta n (a ∘ e)
  | _, _, _, @GluingExpression.separating g h _ _ _ _ x y, d, l, delta, n, a =>
      if g = 2 then
        ∑ split ∈ X.splittings delta, ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
            (remainderContraction X v main x d.1 l.1 split.1 ij.1
                (Option.elim · b (a ∘ Sum.inl)) *
              y.pointContraction X (primaryPointVertex X v)
                d.2 l.2 split.2 ij.2 (Option.elim · b.dual (a ∘ Sum.inr)))
      else if h = 2 then
        ∑ split ∈ X.splittings delta, ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
            (x.pointContraction X (primaryPointVertex X v)
                d.1 l.1 split.1 ij.1 (Option.elim · b (a ∘ Sum.inl)) *
              remainderContraction X v main y d.2 l.2 split.2 ij.2
                (Option.elim · b.dual (a ∘ Sum.inr)))
      else 0
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _, _, _, _ => 0

/-- Reindexing every separating edge preserves the full coefficient contraction.
The terminal agreement is needed only at the used point counts and genus two. -/
theorem remainderContraction_eq (X : SurfaceTarget) (v : Variable X)
    (main : ℕ → SurfaceCotangentVertexValues X ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 2)
    (hx : x.maxComponentGenus = 2) (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hmain : ∀ m, m ≤ n → ∀ (T : Type) [Fintype T] (h : StableArity 2 T)
      (k : T → ℕ) (lt : DecidableEq T) (epsilon : X.Curve) (b : T → SurfaceBasisLabel X),
      main m 2 T h k lt epsilon b =
        SurfacePointPullback.vertex X (coefficientVertex X v) m 2 T h k lt
          (variableCurve v + epsilon) b) :
    remainderContraction X v main x d l delta n a =
      x.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
        d l (variableCurve v + delta) n a := by
  induction x generalizing delta n with
  | fundamental g S h =>
    change g = 2 at hx
    subst g
    rw [remainderContraction, if_pos rfl, GluingExpression.pointContraction]
    exact hmain n le_rfl S h d l delta a
  | relabel e x ih => exact ih hg hx d l delta n (a ∘ e) hmain
  | @separating g h S T _ _ x y ihx ihy =>
    have hmx := x.maxComponentGenus_le
    have hmy := y.maxComponentGenus_le
    change max x.maxComponentGenus y.maxComponentGenus = 2 at hx
    by_cases hxg : g = 2
    · have hxmax : x.maxComponentGenus = 2 := by omega
      rw [remainderContraction, if_pos hxg, primaryPointVertex_eq,
        GluingExpression.pointContraction]
      symm
      trans ∑ split ∈ X.splittings delta, ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
            (x.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
                d.1 l.1 (variableCurve v + split.1) ij.1
                  (Option.elim · b (a ∘ Sum.inl)) *
              y.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
                d.2 l.2 split.2 ij.2 (Option.elim · b.dual (a ∘ Sum.inr)))
      · simp only [Algebra.algebraMap_self_apply]
        apply WeightedCurveClass.sum_splittings_add_left
        intro beta gamma hnot
        apply Finset.sum_eq_zero
        intro b _
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro ij _
        rw [pointContraction_eq_zero_of_not_le v x (by omega) hxmax _ _ _ _ _ hnot,
          zero_mul, mul_zero]
      · apply Finset.sum_congr rfl
        intro split _
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        apply Finset.sum_congr rfl
        intro ij hij
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [ihx (by omega) hxmax _ _ _ _ _ (fun m hm ↦ hmain m (by omega))]
    · have hyg : h = 2 := by omega
      have hymax : y.maxComponentGenus = 2 := by omega
      rw [remainderContraction, if_neg hxg, if_pos hyg, primaryPointVertex_eq,
        GluingExpression.pointContraction]
      symm
      trans ∑ split ∈ X.splittings delta, ∑ b : SurfaceBasisLabel X, b.inverseWeight *
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
            (x.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
                d.1 l.1 split.1 ij.1 (Option.elim · b (a ∘ Sum.inl)) *
              y.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
                d.2 l.2 (variableCurve v + split.2) ij.2
                  (Option.elim · b.dual (a ∘ Sum.inr)))
      · simp only [Algebra.algebraMap_self_apply]
        apply WeightedCurveClass.sum_splittings_add_right
        intro beta gamma hnot
        apply Finset.sum_eq_zero
        intro b _
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro ij _
        rw [pointContraction_eq_zero_of_not_le v y (by omega) hymax _ _ _ _ _ hnot,
          mul_zero, mul_zero]
      · apply Finset.sum_congr rfl
        intro split _
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        apply Finset.sum_congr rfl
        intro ij hij
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        rw [ihy (by omega) hymax _ _ _ _ _ (fun m hm ↦ hmain m (by omega))]
  | nonseparating x ih =>
    have hm := x.maxComponentGenus_le
    change x.maxComponentGenus = 2 at hx
    omega

/-- Signed pullback on the main component, with only the effective remainder
split off along new rational tails. Recursion decreases the added-point count. -/
def remainderVertex (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (n : ℕ) : SurfaceCotangentVertexValues X ℚ :=
  match n with
  | 0 => fun g S _ h d _ delta a ↦ terminal g S h (variableCurve v + delta) d a
  | n + 1 => fun g S _ h d l delta a ↦
      (((GluingExpression.fundamental g S h).addCotangentMarking d l).map fun t ↦
        (t.1 : ℚ) * remainderContraction X v
          (fun m ↦ if _hm : m ≤ n then remainderVertex X v terminal m
            else fun _ _ _ _ _ _ _ _ ↦ 0)
          t.2.expression t.2.decoration t.2.labels delta n (Option.elim · .point a)).sum
termination_by n
decreasing_by omega

/-- Every newly created signed rational tail is included in the translated sum.
The supplied terminal is an implementation of the existing coefficient, not
additional geometric or numerical data. -/
theorem remainderVertex_eq (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (hterminal : terminal = coefficientVertex X v)
    (n : ℕ) : ∀ (S : Type) [Fintype S] (h : StableArity 2 S)
      (d : S → ℕ) (l : DecidableEq S) (delta : X.Curve) (a : S → SurfaceBasisLabel X),
    remainderVertex X v terminal n 2 S h d l delta a =
      SurfacePointPullback.vertex X (coefficientVertex X v) n 2 S h d l
        (variableCurve v + delta) a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S _ h d l delta a
    cases n with
    | zero => simp only [remainderVertex, hterminal, SurfacePointPullback.vertex]
    | succ n =>
      rw [remainderVertex, SurfacePointPullback.vertex_succ]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro t ht
      congr 1
      apply remainderContraction_eq X v _ t.2.expression le_rfl
      · exact (GluingExpression.fundamental 2 S h).addCotangentMarking_maxComponentGenus
          d l t ht
      · intro m hm T _ hT k lT epsilon b
        rw [dif_pos hm]
        exact ih m (by omega) T hT k lT epsilon b

/-- Coefficient at the fixed class plus an explicit effective remainder. -/
def remainderPointCoefficient (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) {S : Type} [Fintype S]
    (z : GluingExpression.CotangentTerm 2 S) (delta : X.Curve)
    (n : ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  if z.expression.maxComponentGenus = 2 then
    remainderContraction X v (remainderVertex X v terminal) z.expression
      z.decoration z.labels delta n a
  else 0

/-- Effective-remainder recursion equals the complete signed point coefficient. -/
theorem remainderPointCoefficient_eq (X : SurfaceTarget) (v : Variable X)
    (terminal : SurfaceVertexValues X ℚ) (hterminal : terminal = coefficientVertex X v)
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm 2 S)
    (delta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    remainderPointCoefficient X v terminal z delta n a =
      pointCoefficient X v z (variableCurve v + delta) n a := by
  by_cases hz : z.expression.maxComponentGenus = 2
  · rw [remainderPointCoefficient, pointCoefficient, if_pos hz, if_pos hz]
    exact remainderContraction_eq X v _ z.expression le_rfl hz _ _ _ _ _
      (fun m _ ↦ remainderVertex_eq X v terminal hterminal m)
  · simp only [remainderPointCoefficient, pointCoefficient, if_neg hz]

end AxiomaticGW.SurfaceGenusTwo
