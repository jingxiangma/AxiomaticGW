/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneScalar
public import AxiomaticGW.Surfaces.CurveSum

/-!
# Dimension pruning of scalar graph contractions

The number of additional point insertions is fixed by the full curve class,
component genus, external labels and number of graph edges. A contraction
with any other number vanishes for every pair of candidate tables. Each
splitting therefore has at most one allowed point distribution, whose full
binomial weight is retained without enumerating impossible distributions.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

/-- Signed number of added points allowed by the surface graph dimension. -/
def requiredPoints (X : SurfaceTarget) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : X.Curve) (a : S → SurfaceBasisLabel X) : ℤ :=
  X.c1Degree beta + (g : ℤ) - 1 + (Fintype.card S : ℤ) -
    (x.graph.graph.edgeCount : ℤ) - ((∑ s, (a s).codimension : ℕ) : ℤ)

private theorem dual_codimension {X : SurfaceTarget} (b : SurfaceBasisLabel X) :
    b.codimension + b.dual.codimension = 2 := by
  cases b <;> rfl

private theorem requiredPoints_relabel {X : SurfaceTarget} {g : ℕ} {S T : Type}
    [Fintype S] [Fintype T] (e : S ≃ T) (x : GluingExpression g S) (beta : X.Curve)
    (a : T → SurfaceBasisLabel X) :
    requiredPoints X (x.relabel e) beta a = requiredPoints X x beta (a ∘ e) := by
  have hs := e.sum_comp (fun t ↦ (a t).codimension)
  simp only [Function.comp_def] at hs ⊢
  unfold requiredPoints
  rw [hs, Fintype.card_congr e]
  rfl

private theorem requiredPoints_separating {X : SurfaceTarget} {g₁ g₂ : ℕ} {S T : Type}
    [Fintype S] [Fintype T] (x : GluingExpression g₁ (Option S))
    (y : GluingExpression g₂ (Option T)) (left right : X.Curve)
    (a : S ⊕ T → SurfaceBasisLabel X) (b : SurfaceBasisLabel X) :
    requiredPoints X x left (Option.elim · b (a ∘ Sum.inl)) +
      requiredPoints X y right (Option.elim · b.dual (a ∘ Sum.inr)) =
        requiredPoints X (x.separating y) (left + right) a := by
  have hb := dual_codimension b
  simp only [requiredPoints, Fintype.sum_option, Fintype.sum_sum_type,
    Fintype.card_option, Fintype.card_sum, Option.elim_none, Option.elim_some,
    Function.comp_def, Nat.cast_add, Nat.cast_one, map_add]
  change _ = _ - ((x.graph.graph.edgeCount + y.graph.graph.edgeCount + 1 : ℕ) : ℤ) - _
  push_cast
  omega

private theorem requiredPoints_nonseparating {X : SurfaceTarget} {g : ℕ} {S : Type}
    [Fintype S] (x : GluingExpression g (Option (Option S))) (beta : X.Curve)
    (a : S → SurfaceBasisLabel X) (b : SurfaceBasisLabel X) :
    requiredPoints X x beta (Option.elim · b (fun t ↦ Option.elim t b.dual a)) =
      requiredPoints X x.nonseparating beta a := by
  have hb := dual_codimension b
  simp only [requiredPoints, Fintype.sum_option, Fintype.card_option,
    Option.elim_none, Option.elim_some, Nat.cast_add, Nat.cast_one]
  change _ = _ - ((x.graph.graph.edgeCount + 1 : ℕ) : ℤ) - _
  push_cast
  omega

/-- Every nonzero contraction has the exact graph dimension, for arbitrary candidates. -/
theorem primaryGraphEval_eq_zero_of_points_ne {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hn : (n : ℤ) ≠ requiredPoints X x beta a) :
    primaryGraphEval X v₀ v₁ x beta n a = 0 := by
  induction x generalizing beta n with
  | fundamental g S h =>
    have hd : ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) ≠
        X.c1Degree beta + (g : ℤ) - 1 + (Fintype.card S : ℤ) := by
      change (n : ℤ) ≠ _ - (0 : ℤ) - _ at hn
      omega
    simp only [primaryGraphEval, primaryScalar, if_neg hd, ite_self]
  | relabel e x ih =>
    exact ih beta n (a ∘ e) (by rwa [requiredPoints_relabel] at hn)
  | @separating g₁ g₂ S T _ _ x y ihx ihy =>
    unfold primaryGraphEval
    apply Finset.sum_eq_zero
    intro left hl
    have hsplit : left + (beta - left) = beta := by
      funext i
      exact Nat.add_sub_of_le (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Fintype.mem_piFinset.mp hl i)))
    apply Finset.sum_eq_zero
    intro b _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ij hij
    apply mul_eq_zero_of_right
    have hc := requiredPoints_separating x y left (beta - left) a b
    rw [hsplit] at hc
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hx : (ij.1 : ℤ) = requiredPoints X x left (Option.elim · b (a ∘ Sum.inl))
    · have hy : (ij.2 : ℤ) ≠
          requiredPoints X y (beta - left) (Option.elim · b.dual (a ∘ Sum.inr)) := by omega
      rw [ihy (beta - left) ij.2 _ hy]
      simp only [mul_zero, ite_self]
    · rw [ihx left ij.1 _ hx, if_pos rfl]
  | nonseparating x ih =>
    unfold primaryGraphEval
    apply Finset.sum_eq_zero
    intro b _
    rw [ih beta n _ (by rwa [requiredPoints_nonseparating]), mul_zero]

private theorem pointDistribution_eq (f h : ℕ → ℚ) (n : ℕ) (k : ℤ)
    (hf : ∀ i : ℕ, (i : ℤ) ≠ k → f i = 0) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (if f ij.1 = 0 then 0 else f ij.1 * h ij.2)) =
      if 0 ≤ k ∧ k ≤ (n : ℤ) then
        (n.choose k.toNat : ℚ) *
          (if f k.toNat = 0 then 0 else f k.toNat * h (n - k.toNat))
      else 0 := by
  by_cases hk : 0 ≤ k ∧ k ≤ (n : ℤ)
  · have hkn : k.toNat ≤ n := Int.toNat_le.mpr hk.2
    rw [if_pos hk]
    apply Finset.sum_eq_single (k.toNat, n - k.toNat)
    · intro ij hij hne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hi : (ij.1 : ℤ) ≠ k := by
        intro he
        have hi : ij.1 = k.toNat := by omega
        apply hne
        exact Prod.ext hi (by omega)
      rw [hf ij.1 hi, if_pos rfl, mul_zero]
    · intro hnot
      exact (hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega))).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro ij hij
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hi : (ij.1 : ℤ) ≠ k := by omega
    rw [hf ij.1 hi, if_pos rfl, mul_zero]

private theorem mulSkipRight_eq (l r : ℚ) :
    (if r = 0 then 0 else l * r) = (if l = 0 then 0 else l * r) := by
  by_cases hr : r = 0
  · simp only [hr, mul_zero, ite_self]
  · by_cases hl : l = 0
    · simp only [hl, zero_mul, ite_self]
    · simp only [if_neg hr, if_neg hl]

/-- Solve the unique possible point distribution at each splitting, retaining its
binomial multiplicity, and prune dimension-incompatible subtrees. Evaluate the
right component first: it is a single vertex in the fixed separating Getzler graphs. -/
def primaryGraphDimensionEval (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → X.Curve → ℕ →
        (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g _ _ _, beta, n, a =>
      primaryScalar X v₀ v₁ g beta n a
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, beta, n, a =>
      primaryGraphDimensionEval X v₀ v₁ x beta n (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, beta, n, a =>
      if (n : ℤ) ≠ requiredPoints X (x.separating y) beta a then 0 else
      X.sumSubcurves beta fun first ↦
        ∑ b : SurfaceBasisLabel X,
        b.inverseWeight *
          (let k := requiredPoints X x first (Option.elim · b (a ∘ Sum.inl))
           if 0 ≤ k ∧ k ≤ (n : ℤ) then
            (n.choose k.toNat : ℚ) *
            (let right := primaryGraphDimensionEval X v₀ v₁ y (beta - first) (n - k.toNat)
                (Option.elim · b.dual (a ∘ Sum.inr))
             if right = 0 then 0 else
               primaryGraphDimensionEval X v₀ v₁ x first k.toNat
                 (Option.elim · b (a ∘ Sum.inl)) * right)
           else 0)
  | _, _, _, @GluingExpression.nonseparating _ _ _ x, beta, n, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        primaryGraphDimensionEval X v₀ v₁ x beta n
          (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- Dimension pruning and selection preserve the original scalar contraction exactly. -/
theorem primaryGraphDimensionEval_eq {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    primaryGraphDimensionEval X v₀ v₁ x beta n a = primaryGraphEval X v₀ v₁ x beta n a := by
  induction x generalizing beta n with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih beta n (a ∘ e)
  | separating x y ihx ihy =>
    by_cases hn : (n : ℤ) ≠ requiredPoints X (x.separating y) beta a
    · rw [primaryGraphDimensionEval, if_pos hn,
        primaryGraphEval_eq_zero_of_points_ne v₀ v₁ _ beta n a hn]
    · simp only [primaryGraphDimensionEval, if_neg hn, SurfaceTarget.sumSubcurves_eq,
        primaryGraphEval, ihx, ihy, mulSkipRight_eq]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      symm
      apply pointDistribution_eq
        (fun i ↦ primaryGraphEval X v₀ v₁ x first i (Option.elim · b (a ∘ Sum.inl)))
        (fun j ↦ primaryGraphEval X v₀ v₁ y (beta - first) j
          (Option.elim · b.dual (a ∘ Sum.inr))) n
        (requiredPoints X x first (Option.elim · b (a ∘ Sum.inl)))
      intro i hi
      exact primaryGraphEval_eq_zero_of_points_ne v₀ v₁ x first i _ hi
  | nonseparating x ih => simp only [primaryGraphDimensionEval, primaryGraphEval, ih]

/-- Preserve the original total-genus-bounded dimension-vanishing API. -/
theorem compactEval_eq_zero_of_points_ne {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 1)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X)
    (hn : (n : ℤ) ≠ requiredPoints X x beta a) :
    compactEval X v₀ v₁ x hg beta n a = 0 :=
  primaryGraphEval_eq_zero_of_points_ne v₀ v₁ x beta n a hn

/-- The original low-genus interface to dimension-pruned primary contraction. -/
def dimensionPrunedEval (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (_hg : g ≤ 1)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  primaryGraphDimensionEval X v₀ v₁ x beta n a

/-- The existing genus-zero/one evaluator retains its exact original meaning. -/
theorem dimensionPrunedEval_eq {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 1)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    dimensionPrunedEval X v₀ v₁ x hg beta n a = compactEval X v₀ v₁ x hg beta n a :=
  primaryGraphDimensionEval_eq v₀ v₁ x beta n a

end AxiomaticGW.SurfaceGenusOne
