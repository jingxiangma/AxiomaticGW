/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroCompactStep

/-!
# Direct scalar replay of primary genus-zero equations

The compact graph is evaluated without constructing intermediate query keys or
polynomial multisets. The vertex formula retains signed dimension, divisor and
classical degree-zero contributions. Its equality theorem proves preservation
of every full-class candidate valuation, and graph induction retains all class
splits, node states and binomial marking multiplicities.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero
open SurfacePolynomialReduction

/-- Zero products can be returned before evaluating the other factor. -/
private theorem mulSkipZero_eq (a b : ℚ) : (if a = 0 then 0 else a * b) = a * b := by
  split_ifs with h
  · rw [h, zero_mul]
  · rfl

/-- Evaluation by full curve class after primary reduction. -/
theorem eval_primaryTerms_curve {X : SurfaceTarget} (v : X.Curve → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 0) (hp : q.IsPrimary) :
    RationalTerms.eval (fun u ↦ v (variableCurve u)) (primaryTerms q) =
      if q.DimensionCompatible then
        if q.beta = 0 then SurfacePrimary.classicalValue q.primaryLabels
        else q.primaryCoefficient * v q.beta
      else 0 := by
  by_cases hd : q.DimensionCompatible
  · by_cases hb : q.beta = 0
    · simp only [primaryTerms, reduceVariable, if_pos hd, hb, ne_eq,
        not_true_eq_false, and_false, ite_false, degreeZeroValue?, hp, hg,
        and_self, ite_true, RationalTerms.eval_term, Multiset.map_zero,
        Multiset.prod_zero, mul_one, one_mul, Algebra.algebraMap_self_apply]
    · by_cases hc : q.primaryCoefficient = 0
      · simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hb),
          if_neg hb, hc, ite_true, RationalTerms.eval_zero, zero_mul]
      · simp only [primaryTerms, reduceVariable, if_pos hd, if_pos (And.intro hp hb),
          if_neg hb, if_neg hc, degreeZeroValue?, RationalTerms.eval_term,
          Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply,
          variableCurve, SurfaceAncestorKey.pointQuery, SurfaceQuery.points]
  · simp only [primaryTerms, reduceVariable, if_neg hd, RationalTerms.eval_zero]

/-- A primary vertex evaluated without query or polynomial terms. Positive-class
candidate zeros short-circuit; classical degree-zero contributions remain independent. -/
def primaryScalar (X : SurfaceTarget) (v : X.Curve → ℚ) (beta : X.Curve) (n : ℕ)
    {S : Type} [Fintype S] (a : S → SurfaceBasisLabel X) : ℚ :=
  if beta ≠ 0 ∧ v beta = 0 then 0 else
  if ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
      X.c1Degree beta - 1 + (Fintype.card S : ℤ) then
    if beta = 0 then
      if n + Fintype.card S = 3 then
        SurfaceCohomology.counit X.blowups
          (SurfaceCohomology.point X.blowups ^ n * ∏ s, (a s).value)
      else 0
    else (∏ s, (a s).primaryFactor beta) * v beta
  else 0

/-- Reindexing all markings preserves the primary scalar, including its
dimension filter, classical product and full-class candidate value. -/
theorem primaryScalar_relabel (X : SurfaceTarget) (v : X.Curve → ℚ) (beta : X.Curve)
    (n : ℕ) {S T : Type} [Fintype S] [Fintype T] (e : S ≃ T)
    (a : T → SurfaceBasisLabel X) :
    primaryScalar X v beta n (a ∘ e) = primaryScalar X v beta n a := by
  have hc := Fintype.card_congr e
  have hsum : (∑ s, (a (e s)).codimension) = ∑ t, (a t).codimension :=
    Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  have hvalue : (∏ s, (a (e s)).value) = ∏ t, (a t).value :=
    Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
  have hfactor : (∏ s, (a (e s)).primaryFactor beta) = ∏ t, (a t).primaryFactor beta :=
    Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
  simp only [primaryScalar, Function.comp_apply, hsum, hvalue, hfactor, hc]

theorem primaryScalar_eq {X : SurfaceTarget} (v : X.Curve → ℚ)
    (S : Type) [Fintype S] (h : StableArity 0 S) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    primaryScalar X v beta n a = RationalTerms.eval (fun u ↦ v (variableCurve u))
      (primaryTerms ((SurfaceAncestorKey.ofLabels 0 S h beta 0 a).addPoints n)) := by
  have hp : ((SurfaceAncestorKey.ofLabels 0 S h beta 0 a).addPoints n).IsPrimary := by
    intro s hs
    rcases Multiset.mem_add.mp hs with hs | hs
    · have he := (Multiset.mem_replicate.mp hs).2
      exact congrArg SurfaceInsertion.psi he
    · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
      rfl
  rw [eval_primaryTerms_curve v _ rfl hp]
  by_cases hz : beta ≠ 0 ∧ v beta = 0
  · simp only [primaryScalar, SurfaceAncestorKey.addPoints,
      SurfaceAncestorKey.ofLabels, if_neg hz.1, hz.2, mul_zero, ite_self]
  · simp only [primaryScalar, if_neg hz, SurfaceAncestorKey.DimensionCompatible,
      SurfaceAncestorKey.totalCodimension, SurfaceAncestorKey.primaryCoefficient,
      SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.addPoints, SurfaceAncestorKey.ofLabels,
      SurfacePrimary.classicalValue, Multiset.map_add, Multiset.map_replicate,
      Multiset.map_map, Function.comp_def, Multiset.sum_add, Multiset.sum_replicate,
      Multiset.prod_add, Multiset.prod_replicate, Multiset.card_add,
      Multiset.card_replicate, Multiset.card_map, Finset.card_val, Finset.card_univ,
      Pi.zero_apply, add_zero, SurfaceBasisLabel.codimension,
      SurfaceBasisLabel.primaryFactor, SurfaceBasisLabel.value, one_pow, one_mul,
      Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul]
    have hd :
        ((∑ s, (a s).codimension : ℕ) : ℤ) + (n : ℤ) =
            X.c1Degree beta - 1 + (Fintype.card S : ℤ) ↔
        (n : ℤ) * 2 + ((∑ s, (a s).codimension : ℕ) : ℤ) =
            X.c1Degree beta - 1 + ((n : ℤ) + (Fintype.card S : ℤ)) := by omega
    simp only [SurfaceBasisLabel.codimension] at hd
    simp only [hd]
    rfl

/-- Direct scalar evaluation of the same compact genus-zero graph. The first
component determines each full splitting, avoiding redundant image comparisons. -/
def compactEval (X : SurfaceTarget) (v : X.Curve → ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] →
      (x : GluingExpression g S) → g = 0 → X.Curve → ℕ →
        (S → SurfaceBasisLabel X) → ℚ
  | _, _, _, @GluingExpression.fundamental _ _ _ _, _, beta, n, a =>
      primaryScalar X v beta n a
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, hg, beta, n, a =>
      compactEval X v x hg beta n (a ∘ e)
  | _, _, _, @GluingExpression.separating _ _ _ _ _ _ x y, hg, beta, n, a =>
      ∑ first ∈ Fintype.piFinset (fun i ↦ Finset.range (beta i + 1)),
        ∑ b : SurfaceBasisLabel X,
        b.inverseWeight *
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
            (let left := compactEval X v x (Nat.eq_zero_of_add_eq_zero_right hg) first ij.1
                (Option.elim · b (a ∘ Sum.inl))
             if left = 0 then 0 else
               left * compactEval X v y (Nat.eq_zero_of_add_eq_zero_left hg) (beta - first) ij.2
                 (Option.elim · b.dual (a ∘ Sum.inr))))
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, hg, _, _, _ =>
      False.elim (Nat.succ_ne_zero _ hg)

/-- No polynomial data are dropped: every scalar value equals the original compact evaluation. -/
theorem compactEval_eq {X : SurfaceTarget} (v : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g = 0)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    compactEval X v x hg beta n a =
      RationalTerms.eval (fun u ↦ v (variableCurve u)) (compactTerms X x hg beta n a) := by
  induction x generalizing beta n with
  | fundamental g S h =>
      subst g
      exact primaryScalar_eq v S h beta n a
  | relabel e x ih => exact ih hg beta n (a ∘ e)
  | separating x y ihx ihy =>
      simp only [compactEval, compactTerms, RationalTerms.eval_sum,
        RationalTerms.eval_scale, RationalTerms.eval_mul, Algebra.algebraMap_self_apply,
        mulSkipZero_eq, ihx, ihy, SurfaceTarget.splittings, WeightedCurveClass.splittings]
      rw [Finset.sum_image]
      intro c _ d _ he
      exact congrArg Prod.fst he
  | nonseparating x ih => omega

/-- Evaluate only scalars. The small energy-three request keeps its existing computation. -/
def scalarReconstructionStep (X : SurfaceTarget) (beta : X.Curve) (v : X.Curve → ℚ) : ℚ :=
  if X.effective.energy beta = 3 then
    compactReconstructionStep X beta (fun u ↦ v (variableCurve u))
  else
    -(∑ i, if WDVV.requested i = 0 then 0 else WDVV.requested i * compactEval X
      (fun gamma ↦ if X.effective.energy gamma < X.effective.energy beta then v gamma else 0)
      (WDVV.expression i) rfl beta (X.effective.energy beta - 4)
      (WDVV.reconstructionLabels X))

/-- Scalar replay preserves the complete held reconstruction equation, including the guard. -/
theorem scalarReconstructionStep_eq (X : SurfaceTarget) (beta : X.Curve) (v : X.Curve → ℚ) :
    scalarReconstructionStep X beta v =
      compactReconstructionStep X beta (fun u ↦ v (variableCurve u)) := by
  unfold scalarReconstructionStep
  split_ifs with hthree
  · rfl
  · simp only [compactReconstructionStep, compactReconstructionTerms,
      compactReconstructionCoefficient, if_neg hthree, div_one, WDVV.compactPrimaryTerms,
      RationalTerms.eval_sum, RationalTerms.eval_scale, Algebra.algebraMap_self_apply,
      mulSkipZero_eq, compactEval_eq]

end AxiomaticGW.SurfaceGenusZero
