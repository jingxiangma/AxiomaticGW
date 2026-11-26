/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCoefficientTerms
public import AxiomaticGW.Surfaces.PointPullbackContraction
public import AxiomaticGW.Tautological.DecoratedGluingMarkingBounds

/-!
# Compressed point pullbacks for genus-two coefficients

A genus-two graph containing a genus-two component has exactly one such
component and only rational complements. On that component extract the
requested normalized coefficient; on every other component use the existing
constant coefficient. The signed point-pullback compression then applies
without constructing every labelled graph placement.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction

/-- A coefficient at genus two and the already reconstructed constant below it.
This is terminal data for contraction, not an additional invariant oracle. -/
def coefficientVertex (X : SurfaceTarget) (v : Variable X) : SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    if g = 2 then
      RationalTerms.coefficient
        (RationalTerms.affineSubstitute normalizedTerms (vertexTerms X g S h beta k a)) {v}
    else RationalTerms.coefficient (vertexTerms X g S h beta k a) 0

/-- Below genus two, the modified contraction retains the original constant. -/
theorem eval_coefficientVertex_genus_lt {X : SurfaceTarget} (v : Variable X)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g < 2)
    (d : x.CotangentDecoration) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedEval X (coefficientVertex X v) d beta k a =
      classConstantCoefficient x d beta k a := by
  induction x generalizing beta with
  | fundamental g S h =>
    simp only [GluingExpression.surfaceDecoratedEval, coefficientVertex, if_neg (by omega : g ≠ 2),
      classConstantCoefficient, GluingExpression.surfaceDecoratedTerms]
  | relabel e x ih => exact ih hg d beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [GluingExpression.surfaceDecoratedEval, classConstantCoefficient,
      GluingExpression.surfaceDecoratedTerms, RationalTerms.coefficient_sum,
      RationalTerms.coefficient_scale, RationalTerms.coefficient_mul_zero,
      Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro pair _
    apply Finset.sum_congr rfl
    intro b _
    rw [ihx (by omega), ihy (by omega)]
    rfl
  | nonseparating x ih =>
    simp only [GluingExpression.surfaceDecoratedEval, classConstantCoefficient,
      GluingExpression.surfaceDecoratedTerms, RationalTerms.coefficient_sum,
      RationalTerms.coefficient_scale, Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (by omega)]
    rfl

/-- With a genus-two component, contraction of the modified terminal values
is exactly the requested coefficient of the full normalized polynomial. -/
theorem eval_coefficientVertex_eq {X : SurfaceTarget} (v : Variable X)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S) (hg : g ≤ 2)
    (hx : x.maxComponentGenus = 2) (d : x.CotangentDecoration)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    x.surfaceDecoratedEval X (coefficientVertex X v) d beta k a =
      normalizedCoefficient x d beta k a v := by
  induction x generalizing beta with
  | fundamental g S h =>
    change g = 2 at hx
    simp only [GluingExpression.surfaceDecoratedEval, coefficientVertex, if_pos hx,
      normalizedCoefficient, GluingExpression.surfaceDecoratedTerms]
  | relabel e x ih => exact ih hg hx d beta (k ∘ e) (a ∘ e)
  | @separating g h S T _ _ x y ihx ihy =>
    have hmx := x.maxComponentGenus_le
    have hmy := y.maxComponentGenus_le
    change max x.maxComponentGenus y.maxComponentGenus = 2 at hx
    rw [normalizedCoefficient_separating x y hg d.1 d.2 beta k a v]
    simp only [GluingExpression.surfaceDecoratedEval, Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro pair _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hxg : g = 2
    · rw [ihx (by omega) (by omega), eval_coefficientVertex_genus_lt v y (by omega),
        normalizedCoefficient_genus_lt y (by omega), mul_zero, zero_add]
    · have hyg : h = 2 := by omega
      rw [ihy (by omega) (by omega), eval_coefficientVertex_genus_lt v x (by omega),
        normalizedCoefficient_genus_lt x (by omega), zero_mul, add_zero]
  | nonseparating x ih =>
    have hm := x.maxComponentGenus_le
    change x.maxComponentGenus = 2 at hx
    omega

/-- Exact coefficient after any number of primary point pullbacks, with
binomial placement counts and every negative cotangent correction. -/
def pointCoefficient (X : SurfaceTarget) (v : Variable X)
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm 2 S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  if z.expression.maxComponentGenus = 2 then
    z.expression.pointContraction X (SurfacePointPullback.vertex X (coefficientVertex X v))
      z.decoration z.labels beta n a
  else 0

/-- Compression is identified with the existing full signed expansion. -/
theorem pointCoefficient_eq {X : SurfaceTarget} (v : Variable X)
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm 2 S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    pointCoefficient X v z beta n a =
      ((z.addMarkings n).map fun t ↦ (t.1 : ℚ) *
        normalizedCoefficient t.2.expression t.2.decoration beta 0
          (SurfaceGenusZero.pointLabels a n) v).sum := by
  by_cases hz : z.expression.maxComponentGenus = 2
  · rw [pointCoefficient, if_pos hz, SurfacePointPullback.contraction_eq]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro t ht
    rw [eval_coefficientVertex_eq v t.2.expression (by omega)
      ((z.addMarkings_maxComponentGenus n t ht).trans hz)]
  · rw [pointCoefficient, if_neg hz]
    symm
    apply Multiset.sum_eq_zero
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hc
    have htmax := z.addMarkings_maxComponentGenus n t ht
    have hzmax := z.expression.maxComponentGenus_le
    rw [← coefficientEval_eq v t.2.expression (by omega),
      coefficientEval_eq_zero_of_maxComponentGenus v t.2.expression (by omega) (by omega), mul_zero]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction

/-- The same BP coefficient with primary point placements compressed. -/
def pointCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) (v : Variable X) : ℚ :=
  ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) * ∑ e,
    SurfaceGenusTwo.pointCoefficient X v (orbitCotangentTerm (Fin.castAdd 16 i) e) beta n a

/-- Every compressed BP entry equals the earlier arbitrary-class evaluator. -/
theorem pointCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 3 → SurfaceBasisLabel X) (v : Variable X) :
    pointCoefficient X n beta a v =
      normalizedCoefficient X n beta 0 (SurfaceGenusZero.pointLabels a n) v := by
  simp only [pointCoefficient, SurfaceGenusTwo.pointCoefficient_eq, normalizedCoefficient,
    SurfaceGenusTwo.coefficientEval_eq]

end AxiomaticGW.BelorousskiPandharipande

namespace AxiomaticGW.L24Relation
open SurfacePolynomialReduction

set_option maxRecDepth 20000

/-- The same compression retains the complete L24 source combination. -/
def pointCoefficient (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) (v : Variable X) : ℚ :=
  (cotangentRelation.map fun t ↦ t.1 *
    SurfaceGenusTwo.pointCoefficient X v t.2 beta n a).sum

/-- Every L24 source weight and signed marking multiplicity is preserved. -/
theorem pointCoefficient_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) (v : Variable X) :
    pointCoefficient X n beta a v =
      normalizedCoefficient X n beta 0 (SurfaceGenusZero.pointLabels a n) v := by
  simp only [pointCoefficient, SurfaceGenusTwo.pointCoefficient_eq, normalizedCoefficient,
    CotangentCombination.pullback, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map, Function.comp_def, mul_assoc, Multiset.sum_map_mul_left,
    SurfaceGenusTwo.coefficientEval_eq]

end AxiomaticGW.L24Relation
