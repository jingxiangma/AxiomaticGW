/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoLeading

/-!
# Coefficients across curve classes in genus-two equations

The input-class leading matrix need not determine the primary sector. This
evaluator also extracts coefficients at smaller full curve classes, retaining
positive-class rational components and ancestor-normalization corrections.
Its equality theorem refers to the complete normalized contraction. It does
not assert a recurrence or supply any genus-two value.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
variable {X : SurfaceTarget}

/-- The constant coefficient before normalizing residual ancestors, at any class. -/
def classConstantCoefficient {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.coefficient (x.surfaceDecoratedTerms X (vertexTerms X) d beta k a) 0

/-- The exact singleton coefficient after the full ancestor normalization. -/
def normalizedCoefficient {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (d : x.CotangentDecoration) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (v : Variable X) : ℚ :=
  RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
    (x.surfaceDecoratedTerms X (vertexTerms X) d beta k a)) {v}

theorem normalizedCoefficient_genus_lt {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g < 2) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) (v : Variable X) :
    normalizedCoefficient x d beta k a v = 0 :=
  (termsBound_decorated x d beta k a).substituted_coefficient_eq_zero_of_genus_lt
    hg normalizedTerms v

theorem normalizedCoefficient_fundamental (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (hg : g ≤ 2) (d : S → ℕ) (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) (v : Variable X) :
    normalizedCoefficient (.fundamental g S h) d beta k a v =
      if g = 2 then
        let q := SurfaceAncestorKey.ofLabels g S h beta (k + d) a
        if q.DimensionCompatible then
          RationalTerms.coefficient (normalizedTerms q) {v} else 0
      else 0 := by
  by_cases htwo : g = 2
  · subst g
    simp only [normalizedCoefficient, GluingExpression.surfaceDecoratedTerms, vertexTerms,
      residualTerms, SurfaceAncestorKey.ofLabels, Nat.reduceLeDiff, if_false, if_true]
    split_ifs with hd
    · rw [RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
        Multiset.sum_singleton, one_mul]
    · exact RationalTerms.coefficient_affineSubstitute_zero _ _
  · rw [if_neg htwo]
    exact normalizedCoefficient_genus_lt (.fundamental g S h) (by omega) d beta k a v

/-- The constant-factor rule holds over every ordered full-class splitting.
No equality between the requested variable's class and the input class is required. -/
theorem normalizedCoefficient_separating {g h : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (x : GluingExpression g (Option S)) (y : GluingExpression h (Option T))
    (hgen : g + h ≤ 2) (dx : x.CotangentDecoration) (dy : y.CotangentDecoration)
    (beta : X.Curve) (k : S ⊕ T → ℕ) (a : S ⊕ T → SurfaceBasisLabel X)
    (v : Variable X) :
    normalizedCoefficient (x.separating y) (dx, dy) beta k a v =
      ∑ pair ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        (classConstantCoefficient x dx pair.1 (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) *
          normalizedCoefficient y dy pair.2 (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr)) v +
        normalizedCoefficient x dx pair.1 (PsiClasses.separatingLeftPowers k)
            (Option.elim · b (a ∘ Sum.inl)) v *
          classConstantCoefficient y dy pair.2 (PsiClasses.separatingRightPowers k)
            (Option.elim · b.dual (a ∘ Sum.inr))) := by
  unfold normalizedCoefficient
  simp only [GluingExpression.surfaceDecoratedTerms,
    RationalTerms.coefficient_affineSubstitute_sum,
    RationalTerms.coefficient_affineSubstitute_scale]
  apply Finset.sum_congr rfl
  intro pair _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact RationalTerms.coefficient_affineSubstitute_mul normalizedTerms _ _ v
    ((termsBound_decorated x dx pair.1 _ _).constant_factor
      (termsBound_decorated y dy pair.2 _ _) hgen)

theorem normalizedCoefficient_nonseparating {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g (Option (Option S))) (hg : g + 1 ≤ 2)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) (v : Variable X) :
    normalizedCoefficient x.nonseparating d beta k a v = 0 := by
  simp only [normalizedCoefficient, GluingExpression.surfaceDecoratedTerms,
    RationalTerms.coefficient_affineSubstitute_sum,
    RationalTerms.coefficient_affineSubstitute_scale]
  apply Finset.sum_eq_zero
  intro b _
  rw [(termsBound_decorated x d beta _ _).substituted_coefficient_eq_zero_of_genus_lt
    (by omega) normalizedTerms v, mul_zero]

/-- Extract any normalized coefficient while evaluating only components on a
genus-two branch. A zero branch is tested before its rational complement. -/
def coefficientEval (X : SurfaceTarget) (v : Variable X) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g ≤ 2 → x.CotangentDecoration → X.Curve →
        (S → ℕ) → (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, _, d, beta, k, a =>
      if g = 2 then
        let q := SurfaceAncestorKey.ofLabels g S h beta (k + d) a
        if q.DimensionCompatible then
          RationalTerms.coefficient (normalizedTerms q) {v} else 0
      else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, d, beta, k, a =>
      coefficientEval X v x hg d beta (k ∘ e) (a ∘ e)
  | _, _, _, @GluingExpression.separating g h _ _ _ _ x y, hg, d, beta, k, a =>
      if g = 2 then
        ∑ pair ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
          let c := coefficientEval X v x (by omega) d.1 pair.1
            (PsiClasses.separatingLeftPowers k) (Option.elim · b (a ∘ Sum.inl))
          if c = 0 then 0 else b.inverseWeight * c *
            classConstantCoefficient y d.2 pair.2 (PsiClasses.separatingRightPowers k)
              (Option.elim · b.dual (a ∘ Sum.inr))
      else if h = 2 then
        ∑ pair ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
          let c := coefficientEval X v y (by omega) d.2 pair.2
            (PsiClasses.separatingRightPowers k) (Option.elim · b.dual (a ∘ Sum.inr))
          if c = 0 then 0 else b.inverseWeight *
            classConstantCoefficient x d.1 pair.1 (PsiClasses.separatingLeftPowers k)
              (Option.elim · b (a ∘ Sum.inl)) * c
      else 0
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _, _, _, _ => 0

/-- Correctness at every full curve class, including all normalization tails. -/
theorem coefficientEval_eq (v : Variable X) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hg : g ≤ 2) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    coefficientEval X v x hg d beta k a = normalizedCoefficient x d beta k a v := by
  induction x generalizing beta with
  | fundamental g S h => exact (normalizedCoefficient_fundamental g S h hg d beta k a v).symm
  | relabel e x ih => exact ih hg d beta (k ∘ e) (a ∘ e)
  | @separating g h S T _ _ x y ihx ihy =>
    rw [normalizedCoefficient_separating x y hg d.1 d.2 beta k a v]
    by_cases hx : g = 2
    · simp only [coefficientEval, if_pos hx, ihx,
        normalizedCoefficient_genus_lt y (by omega), mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro pair _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with hc
      · rw [hc, zero_mul, mul_zero]
      · exact mul_assoc _ _ _
    · by_cases hy : h = 2
      · simp only [coefficientEval, if_neg hx, if_pos hy, ihy,
          normalizedCoefficient_genus_lt x (by omega), zero_mul, add_zero]
        apply Finset.sum_congr rfl
        intro pair _
        apply Finset.sum_congr rfl
        intro b _
        split_ifs with hc
        · rw [hc, mul_zero, mul_zero]
        · exact mul_assoc _ _ _
      · simp only [coefficientEval, if_neg hx, if_neg hy,
          normalizedCoefficient_genus_lt x (by omega), normalizedCoefficient_genus_lt y (by omega),
          zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
  | nonseparating x ih => exact (normalizedCoefficient_nonseparating x hg d beta k a v).symm

/-- A diagram without a genus-two component has no residual singleton coefficient,
even when its total genus is two because of loops or several elliptic vertices. -/
theorem coefficientEval_eq_zero_of_maxComponentGenus (v : Variable X)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 2)
    (hx : x.maxComponentGenus ≤ 1) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    coefficientEval X v x hg d beta k a = 0 := by
  induction x generalizing beta with
  | fundamental g S h =>
    have hne : g ≠ 2 := by change g ≤ 1 at hx; omega
    simp only [coefficientEval, if_neg hne]
  | relabel e x ih => exact ih hg hx d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    change max x.maxComponentGenus y.maxComponentGenus ≤ 1 at hx
    simp only [coefficientEval, ihx _ (max_le_iff.mp hx).1,
      ihy _ (max_le_iff.mp hx).2, ite_true, Finset.sum_const_zero, ite_self]
  | nonseparating x ih => rfl

end AxiomaticGW.SurfaceGenusTwo
