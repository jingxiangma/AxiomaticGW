/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneNormalization
public import AxiomaticGW.Surfaces.GenusTwoPointCoefficients

/-!
# Plane coefficients with exact component-class pruning

The complete plane normalization has no calibration tail. A genus-two
component can therefore contribute to a requested coefficient only at that
same full curve class. Check this condition before reducing its insertions.
The resulting contraction is proved equal to the complete generic evaluator;
positive rational complements and signed stable-curve pullbacks remain.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction

/-- Reject a different component class before running direct plane normalization. -/
def planeCoefficientVertex (v : Variable .plane) : SurfaceVertexValues .plane ℚ :=
  fun g S _ h beta k a ↦
    if g = 2 then
      if SurfaceGenusZero.variableCurve v = beta then
        let q := SurfaceAncestorKey.ofLabels g S h beta k a
        if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
        else 0
      else 0
    else RationalTerms.coefficient (vertexTerms .plane g S h beta k a) 0

/-- Plane class pruning and calibration cancellation preserve the original component. -/
theorem planeCoefficientVertex_eq (v : Variable .plane) :
    planeCoefficientVertex v = coefficientVertex .plane v := by
  funext g S _ h beta k a
  unfold planeCoefficientVertex coefficientVertex
  by_cases hg : g = 2
  · subst g
    rw [if_pos rfl, if_pos rfl]
    let q := SurfaceAncestorKey.ofLabels 2 S h beta k a
    change (if SurfaceGenusZero.variableCurve v = beta then
        if q.DimensionCompatible then RationalTerms.coefficient (directNormalizedTerms q) {v}
        else 0
      else 0) = RationalTerms.coefficient
        (RationalTerms.affineSubstitute normalizedTerms (residualTerms q)) {v}
    unfold residualTerms
    by_cases hd : q.DimensionCompatible
    · simp only [if_pos hd, if_neg (show ¬q.genus ≤ 1 from Nat.not_succ_le_self 1)]
      rw [RationalTerms.coefficient_affineSubstitute_term, Multiset.map_singleton,
        Multiset.sum_singleton, one_mul, normalizedTerms_plane_eq_direct]
      split_ifs with hb
      · rfl
      · exact (coefficient_directNormalizedTerms_eq_zero q le_rfl v hb).symm
    · simp only [if_neg hd, ite_self, RationalTerms.coefficient_affineSubstitute_zero]
  · rw [if_neg hg, if_neg hg]

/-- Complete signed point contraction with the proved plane component shortcut. -/
def planePointCoefficient (v : Variable .plane)
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm 2 S)
    (beta : SurfaceTarget.plane.Curve) (n : ℕ) (a : S → SurfaceBasisLabel .plane) : ℚ :=
  if z.expression.maxComponentGenus = 2 then
    z.expression.pointContraction .plane
      (SurfacePointPullback.vertex .plane (planeCoefficientVertex v))
        z.decoration z.labels beta n a
  else 0

/-- Every original graph, signed correction and full curve split is retained. -/
theorem planePointCoefficient_eq (v : Variable .plane)
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm 2 S)
    (beta : SurfaceTarget.plane.Curve) (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    planePointCoefficient v z beta n a = pointCoefficient .plane v z beta n a := by
  rw [planePointCoefficient, planeCoefficientVertex_eq]
  rfl

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction

/-- The original BP coefficient, with plane component classes checked first. -/
def planePointCoefficient (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) : ℚ :=
  ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) * ∑ e,
    SurfaceGenusTwo.planePointCoefficient v (orbitCotangentTerm (Fin.castAdd 16 i) e) beta n a

/-- This plane implementation equals the previously proved full coefficient consumer. -/
theorem planePointCoefficient_eq (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) :
    planePointCoefficient n beta a v = pointCoefficient .plane n beta a v := by
  simp only [planePointCoefficient, SurfaceGenusTwo.planePointCoefficient_eq, pointCoefficient]

end AxiomaticGW.BelorousskiPandharipande
