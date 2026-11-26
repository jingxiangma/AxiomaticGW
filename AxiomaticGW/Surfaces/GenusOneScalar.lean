/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneCompactStep

/-!
# Direct scalar replay of primary Getzler equations

The evaluator preserves genus-zero and genus-one candidates separately and
uses the existing classical and elliptic degree-zero constants. It evaluates
binomial marking distributions and all full-class/node contractions without
constructing intermediate polynomial multisets.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne
open SurfacePolynomialReduction SurfaceLowGenus
open SurfaceGenusZero (variableCurve)

/-- Zero products can be returned before evaluating the other factor. -/
private theorem mulSkipZero_eq (a b : ℚ) : (if a = 0 then 0 else a * b) = a * b := by
  split_ifs with h
  · rw [h, zero_mul]
  · rfl

/-- Evaluation by full curve class after primary reduction. -/
theorem eval_primaryTerms_curve {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus ≤ 1) (hp : q.IsPrimary) :
    RationalTerms.eval (pointValuation v₀ v₁) (primaryTerms q) =
      if q.DimensionCompatible then
        if q.beta = 0 then
          if q.genus = 0 then SurfacePrimary.classicalValue q.primaryLabels
          else SurfacePrimary.genusOneZeroValue q.primaryLabels
        else q.primaryCoefficient * (if q.genus = 0 then v₀ q.beta else v₁ q.beta)
      else 0 := by
  by_cases hd : q.DimensionCompatible
  · by_cases hb : q.beta = 0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with hg | hg
      · simp only [primaryTerms, reduceVariable, if_pos hd, hb, ne_eq,
          not_true_eq_false, and_false, ite_false, degreeZeroValue?, hp, hg,
          and_self, ite_true, RationalTerms.eval_term, Multiset.map_zero,
          Multiset.prod_zero, mul_one, one_mul, Algebra.algebraMap_self_apply]
      · simp only [primaryTerms, reduceVariable, if_pos hd, hb, ne_eq,
          not_true_eq_false, and_false, ite_false, degreeZeroValue?, hp, hg,
          and_self, ite_true, Nat.one_ne_zero, RationalTerms.eval_term, Multiset.map_zero,
          Multiset.prod_zero, mul_one, one_mul, Algebra.algebraMap_self_apply]
    · by_cases hc : q.primaryCoefficient = 0
      · simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hb),
          if_neg hb, hc, ite_true, RationalTerms.eval_zero, zero_mul]
      · simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hb),
          if_neg hb, if_neg hc, degreeZeroValue?, RationalTerms.eval_term,
          Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply,
          pointValuation, variableGenus, variableCurve, SurfaceAncestorKey.pointQuery,
          SurfaceQuery.points]
  · simp only [primaryTerms, reduceVariable, if_neg hd, RationalTerms.eval_zero]

/-- A primary vertex evaluated without query or polynomial terms. Positive-class
candidate zeros short-circuit; both degree-zero sectors remain independent. -/
def primaryScalar (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) (g : ℕ) (beta : X.Curve) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) : ℚ :=
  if beta ≠ 0 ∧ (if g = 0 then v₀ beta else v₁ beta) = 0 then 0 else
  if ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
      X.c1Degree beta + (g : ℤ) - 1 + (Fintype.card S : ℤ) then
    if beta = 0 then
      if g = 0 then
        if n + Fintype.card S = 3 then
          SurfaceCohomology.counit X.blowups
            (SurfaceCohomology.point X.blowups ^ n * ∏ s, (a s).value)
        else 0
      else if n + Fintype.card S = 1 then ∑ s, (a s).genusOneZeroValue else 0
    else (∏ s, (a s).primaryFactor beta) * (if g = 0 then v₀ beta else v₁ beta)
  else 0

theorem primaryScalar_eq {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (hg : g ≤ 1) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    primaryScalar X v₀ v₁ g beta n a = RationalTerms.eval (pointValuation v₀ v₁)
      (primaryTerms ((SurfaceAncestorKey.ofLabels g S h beta 0 a).addPoints n)) := by
  have hp : ((SurfaceAncestorKey.ofLabels g S h beta 0 a).addPoints n).IsPrimary := by
    intro s hs
    rcases Multiset.mem_add.mp hs with hs | hs
    · have he := (Multiset.mem_replicate.mp hs).2
      exact congrArg SurfaceInsertion.psi he
    · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
      rfl
  rw [eval_primaryTerms_curve v₀ v₁ _ hg hp]
  by_cases hz : beta ≠ 0 ∧ (if g = 0 then v₀ beta else v₁ beta) = 0
  · simp only [primaryScalar, SurfaceAncestorKey.addPoints,
      SurfaceAncestorKey.ofLabels, if_neg hz.1, hz.2, mul_zero, ite_self]
  · simp only [primaryScalar, if_neg hz, SurfaceAncestorKey.DimensionCompatible,
      SurfaceAncestorKey.totalCodimension, SurfaceAncestorKey.primaryCoefficient,
      SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels,
      SurfacePrimary.classicalValue, SurfacePrimary.genusOneZeroValue,
      SurfaceBasisLabel.genusOneZeroValue, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_map, Function.comp_def, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.prod_add, Multiset.prod_replicate, Multiset.card_add,
      Multiset.card_replicate, Multiset.card_map, Finset.card_val, Finset.card_univ,
      Pi.zero_apply, add_zero, SurfaceBasisLabel.codimension,
      SurfaceBasisLabel.primaryFactor, SurfaceBasisLabel.value, one_pow, one_mul,
      mul_zero, zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul]
    have hd :
        ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
            X.c1Degree beta + (g : ℤ) - 1 + (Fintype.card S : ℤ) ↔
        (n : ℤ) * 2 + ((∑ s, (a s).codimension : ℕ) : ℤ) =
            X.c1Degree beta + (g : ℤ) - 1 + ((n : ℤ) + (Fintype.card S : ℤ)) := by omega
    simp only [SurfaceBasisLabel.codimension] at hd
    simp only [hd]
    rfl

/-- Primary scalar contraction without a total-genus restriction. Its low-genus
interpretation requires every component, rather than the whole graph, to have
genus at most one. All full classes, node states and binomial weights remain. -/
def primaryGraphEval (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → X.Curve → ℕ →
        (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental g _ _ _, beta, n, a =>
      primaryScalar X v₀ v₁ g beta n a
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, beta, n, a =>
      primaryGraphEval X v₀ v₁ x beta n (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, beta, n, a =>
      ∑ first ∈ Fintype.piFinset (fun i ↦ Finset.range (beta i + 1)),
        ∑ b : SurfaceBasisLabel X,
        b.inverseWeight *
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
            (let left := primaryGraphEval X v₀ v₁ x first ij.1
                (Option.elim · b (a ∘ Sum.inl))
             if left = 0 then 0 else
               left * primaryGraphEval X v₀ v₁ y (beta - first) ij.2
                 (Option.elim · b.dual (a ∘ Sum.inr))))
  | _, _, _, @GluingExpression.nonseparating _ _ _ x, beta, n, a =>
      ∑ b : SurfaceBasisLabel X, b.inverseWeight *
        primaryGraphEval X v₀ v₁ x beta n
          (Option.elim · b (fun t ↦ Option.elim t b.dual a))

/-- The original genus-zero/one scalar interface uses the same graph contraction. -/
def compactEval (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (_hg : g ≤ 1)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  primaryGraphEval X v₀ v₁ x beta n a

/-- Direct scalar evaluation equals the full compressed polynomial for every candidate pair. -/
theorem compactEval_eq {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 1)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    compactEval X v₀ v₁ x hg beta n a =
      RationalTerms.eval (pointValuation v₀ v₁)
        (SurfacePointExpansion.compactTerms X x beta n a) := by
  induction x generalizing beta n with
  | fundamental g S h => exact primaryScalar_eq v₀ v₁ g S h hg beta n a
  | relabel e x ih => exact ih hg beta n (a ∘ e)
  | separating x y ihx ihy =>
      change primaryGraphEval X v₀ v₁ _ _ _ _ = _
      simp only [compactEval] at ihx ihy
      simp only [primaryGraphEval, SurfacePointExpansion.compactTerms, RationalTerms.eval_sum,
        RationalTerms.eval_scale, RationalTerms.eval_mul, Algebra.algebraMap_self_apply,
        mulSkipZero_eq, ihx (by omega), ihy (by omega), SurfaceTarget.splittings,
        WeightedCurveClass.splittings]
      rw [Finset.sum_image]
      intro c _ d _ he
      exact congrArg Prod.fst he
  | nonseparating x ih =>
      change primaryGraphEval X v₀ v₁ _ _ _ _ = _
      simp only [compactEval] at ih
      simp only [primaryGraphEval, SurfacePointExpansion.compactTerms, RationalTerms.eval_sum,
        RationalTerms.eval_scale, Algebra.algebraMap_self_apply, ih (by omega)]

/-- Evaluate the selected original equation by scalars, guarding only the elliptic candidates. -/
def scalarReconstructionStep (X : SurfaceTarget) (beta : X.Curve)
    (v₀ v₁ : X.Curve → ℚ) : ℚ :=
  (∑ i, if GetzlerGraphs.requested i = 0 then 0 else
    GetzlerGraphs.requested i * compactEval X v₀
      (fun gamma ↦ if X.effective.energy gamma < X.effective.energy beta then v₁ gamma else 0)
      (GetzlerGraphs.expression i) (by omega) beta (X.effective.energy beta - 2)
      (GetzlerGraphs.reconstructionLabels X)) / 9

/-- Scalar replay retains the exact original remainder, including same-energy rational terms. -/
theorem scalarReconstructionStep_eq (X : SurfaceTarget) (beta : X.Curve)
    (v₀ v₁ : X.Curve → ℚ) :
    scalarReconstructionStep X beta v₀ v₁ =
      compactReconstructionStep X beta (pointValuation v₀ v₁) := by
  have hw : pointValuation v₀
      (fun gamma ↦ if X.effective.energy gamma < X.effective.energy beta then v₁ gamma else 0) =
      (fun u ↦ if variableGenus u = 0 ∨
        X.effective.energy (variableCurve u) < X.effective.energy beta then
        pointValuation v₀ v₁ u else 0) := by
    funext u
    unfold pointValuation
    by_cases hg : variableGenus u = 0
    · simp only [hg, ite_true, true_or]
    · simp only [hg, ite_false, false_or]
  simp only [scalarReconstructionStep, compactReconstructionStep,
    GetzlerGraphs.compactPrimaryTerms, RationalTerms.eval_sum, RationalTerms.eval_scale,
    Algebra.algebraMap_self_apply, mulSkipZero_eq, compactEval_eq, hw]

end AxiomaticGW.SurfaceGenusOne
