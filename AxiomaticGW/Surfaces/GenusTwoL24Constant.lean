/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoConstant
public import AxiomaticGW.Surfaces.GenusTwoNormalizedL24

/-!
# Scalar constants of the complete normalized L24 equations

Normalization preserves the constant because every residual genus-two term
is a singleton, including all signed calibration tails and higher ancestors.
The scalar point contraction retains the complete original decorated relation
and every counted marking. It reconstructs lower-genus components with the
existing algorithms; no candidate genus-two value is supplied.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open SurfacePolynomialReduction

-- The unchanged source dispatch has 815 columns.
set_option maxRecDepth 20000

/-- Every target and arbitrary external powers preserve the complete L24 constant.
Signed calibration tails are kept as singleton variables and evaluated at zero. -/
theorem eval_zero_normalizedGenusTwoTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedGenusTwoTerms X n beta k a) =
      RationalTerms.eval (fun _ ↦ (0 : ℚ)) (genusTwoTerms X n beta k a) := by
  rw [normalizedGenusTwoTerms, RationalTerms.eval_affineSubstitute
    (fun _ ↦ (0 : ℚ)) (fun q ↦ RationalTerms.eval (fun _ ↦ (0 : ℚ)) (normalizedTerms q))
    normalizedTerms (fun _ ↦ rfl) _ (genusTwoTerms_card_le_one X n beta k a)]
  apply RationalTerms.eval_congr
  intro t ht q hq
  have hg := ((genusTwoTerms_bound X n beta k a) t ht).dependency q hq
  exact eval_zero_normalizedTerms q (by omega)

/-- Compress only added primary points in the complete original decorated L24 constant. -/
def pointConstant (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  (cotangentRelation.map fun t ↦ t.1 *
    t.2.expression.pointContraction X
      (SurfacePointPullback.vertex X (SurfaceGenusTwo.constantVertex X))
      t.2.decoration t.2.labels beta n a).sum

/-- The scalar contraction equals the constant of the entire unnormalized L24 polynomial. -/
theorem pointConstant_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstant X n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (genusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) := by
  rw [genusTwoTerms, eval_surfaceTerms]
  simp only [SurfaceGenusTwo.eval_zero_vertexTerms, Algebra.algebraMap_self_apply,
    pointConstant, SurfacePointPullback.contraction_eq, CotangentCombination.pullback,
    Multiset.map_bind, Multiset.sum_bind, Multiset.map_map, Function.comp_def,
    Multiset.sum_map_mul_left, mul_assoc]

/-- Complete ancestor normalization changes none of the scalar constant, on either blowup. -/
theorem pointConstant_eq_normalized (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstant X n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) := by
  rw [eval_zero_normalizedGenusTwoTerms, pointConstant_eq]

end AxiomaticGW.L24Relation
