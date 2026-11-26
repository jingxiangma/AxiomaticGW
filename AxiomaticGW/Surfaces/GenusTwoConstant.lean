/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneNormalization
public import AxiomaticGW.Surfaces.GenusTwoNormalizedBP
public import AxiomaticGW.Surfaces.PointPullbackContraction

/-!
# Scalar constant terms of the complete BP equations

Setting residual genus-two variables to zero leaves exactly the previously
reconstructed lower-genus components. Scalar contraction avoids constructing
and then normalizing the polynomial variables which are discarded. Signed
point pullbacks retain every original diagram and marking multiplicity.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Reconstruct lower genera and set higher-genus residual variables to zero.
The dimension guard and both lower-genus algorithms are unchanged. -/
def constantVertex (X : SurfaceTarget) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    if g ≤ 1 then
      let q := SurfaceAncestorKey.ofLabels g S h beta k a
      if q.DimensionCompatible then
        SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q
      else 0
    else 0

/-- Scalar terminal values are the exact zero valuation of the original terms. -/
theorem eval_zero_vertexTerms (X : SurfaceTarget) (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (vertexTerms X g S h beta k a) =
      constantVertex X g S h beta k a := by
  unfold vertexTerms residualTerms constantVertex
  by_cases hg : g ≤ 1 <;>
    simp only [SurfaceAncestorKey.ofLabels, hg, ite_true, ite_false]
  all_goals split_ifs <;>
    simp only [RationalTerms.eval_term, RationalTerms.eval_zero,
      Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
      Multiset.prod_singleton, Algebra.algebraMap_self_apply, mul_one, mul_zero]

/-- A graph with a higher-genus component contributes no lower-genus constant. -/
theorem constant_contraction_eq_zero (X : SurfaceTarget) {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (hx : 2 ≤ x.maxComponentGenus)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedEval X (constantVertex X) d beta k a = 0 := by
  induction x generalizing beta with
  | fundamental g S h =>
    change 2 ≤ g at hx
    rw [GluingExpression.surfaceDecoratedEval, constantVertex, if_neg (by omega)]
  | relabel e x ih => exact ih hx d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    change 2 ≤ max x.maxComponentGenus y.maxComponentGenus at hx
    rcases le_max_iff.mp hx with hx | hy
    · simp only [GluingExpression.surfaceDecoratedEval, ihx hx, zero_mul, mul_zero,
        Finset.sum_const_zero]
    · simp only [GluingExpression.surfaceDecoratedEval, ihy hy, mul_zero,
        Finset.sum_const_zero]
  | nonseparating x ih =>
    simp only [GluingExpression.surfaceDecoratedEval, ih hx, mul_zero,
      Finset.sum_const_zero]

/-- Signed point pullbacks preserve that vanishing, including all new tails. -/
theorem point_constant_eq_zero (X : SurfaceTarget) {g : ℕ} {S : Type} [Fintype S]
    (z : GluingExpression.CotangentTerm g S) (hz : 2 ≤ z.expression.maxComponentGenus)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    z.expression.pointContraction X (SurfacePointPullback.vertex X (constantVertex X))
      z.decoration z.labels beta n a = 0 := by
  rw [SurfacePointPullback.contraction_eq]
  apply Multiset.sum_eq_zero
  intro c hc
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
  rw [constant_contraction_eq_zero X t.2.expression
    ((z.addMarkings_maxComponentGenus n t ht) ▸ hz), mul_zero]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.SurfacePolynomialReduction

/-- The existing plane interface is the specialization of generic singleton support. -/
theorem eval_zero_normalizedTerms_plane (q : SurfaceAncestorKey .plane) (hg : 2 ≤ q.genus) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedTerms q) = 0 :=
  eval_zero_normalizedTerms q hg

end AxiomaticGW.SurfacePolynomialReduction

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction

/-- The full constant survives normalization on every target and at arbitrary powers.
Each signed residual correction remains a singleton and vanishes only under zero valuation. -/
theorem eval_zero_normalizedGenusTwoTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedGenusTwoTerms X n beta k a) =
      RationalTerms.eval (fun _ ↦ (0 : ℚ)) (genusTwoTerms X n beta k a) := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute
    (fun _ ↦ (0 : ℚ)) (fun q ↦ RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedTerms q))
    normalizedTerms (fun _ ↦ rfl) _ (genusTwoTerms_card_le_one X n beta k a)]
  apply RationalTerms.eval_congr
  intro t ht q hq
  have hg := ((genusTwoTerms_bound X n beta k a) t ht).dependency q hq
  exact eval_zero_normalizedTerms q (by omega)

/-- Preserve the original plane constant-normalization interface. -/
theorem eval_zero_normalizedGenusTwoTerms_plane (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel .plane) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedGenusTwoTerms .plane n beta k a) =
      RationalTerms.eval (fun _ ↦ (0 : ℚ)) (genusTwoTerms .plane n beta k a) :=
  eval_zero_normalizedGenusTwoTerms .plane n beta k a

/-- The complete lower-genus contribution with compressed primary point placements. -/
def pointConstant (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  ∑ i, rawPaperCoefficient i * ∑ e,
    let z := orbitCotangentTerm i e
    z.expression.pointContraction X
      (SurfacePointPullback.vertex X (SurfaceGenusTwo.constantVertex X))
      z.decoration z.labels beta n a

/-- Scalar contraction is bound to the constant of the complete original BP polynomial. -/
theorem pointConstant_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) :
    pointConstant X n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (genusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) := by
  rw [genusTwoTerms, eval_surfaceTerms]
  simp only [pointConstant, rawPaperCoefficient_eq, Algebra.algebraMap_self_apply,
    SurfaceGenusTwo.eval_zero_vertexTerms, SurfacePointPullback.contraction_eq]

/-- The same scalar is the constant after full ancestor normalization on every target. -/
theorem pointConstant_eq_normalized (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) :
    pointConstant X n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) := by
  rw [eval_zero_normalizedGenusTwoTerms, pointConstant_eq]

/-- Preserve the original plane scalar interface after generic constant normalization. -/
theorem pointConstant_plane_eq (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) :
    pointConstant .plane n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms .plane n beta 0 (SurfaceGenusZero.pointLabels a n)) :=
  pointConstant_eq_normalized .plane n beta a

end AxiomaticGW.BelorousskiPandharipande
