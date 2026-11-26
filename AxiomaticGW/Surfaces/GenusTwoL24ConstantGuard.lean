/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoL24Constant
public import AxiomaticGW.Surfaces.ScalarPointContraction

/-!
# Guarding genus-two components before scalar L24 contraction

A retained component of genus at least two has zero constant under the existing
zero valuation. The guard avoids computing any scalar contractions of that
entire term; lower-genus terms retain all splits, signed tails and weights.
This upward evaluator does not change the original constant or its imports.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Skip an entire term when a retained higher-genus component makes its
constant zero; otherwise use the existing zero-product scalar evaluator. -/
def guardedConstantPointContraction (X : SurfaceTarget) {g : ℕ} {S : Type}
    [Fintype S] (z : GluingExpression.CotangentTerm g S) (beta : X.Curve)
    (n : ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  if 2 ≤ z.expression.maxComponentGenus then 0 else
    z.expression.scalarPointContraction X
      (SurfacePointPullback.vertex X (constantVertex X))
      z.decoration z.labels beta n a

/-- The early branch requires no class, energy or marking positivity premise. -/
theorem guardedConstantPointContraction_eq_zero (X : SurfaceTarget) {g : ℕ}
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (hz : 2 ≤ z.expression.maxComponentGenus) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    guardedConstantPointContraction X z beta n a = 0 := by
  rw [guardedConstantPointContraction, if_pos hz]

/-- Lower-genus terms keep the existing scalar contraction, including at
class zero and with no added markings. -/
theorem guardedConstantPointContraction_of_lt (X : SurfaceTarget) {g : ℕ}
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (hz : z.expression.maxComponentGenus < 2) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    guardedConstantPointContraction X z beta n a =
      z.expression.scalarPointContraction X
        (SurfacePointPullback.vertex X (constantVertex X))
        z.decoration z.labels beta n a := by
  rw [guardedConstantPointContraction, if_neg (not_le_of_gt hz)]

/-- The guard computes exactly the original full signed point contraction. -/
theorem guardedConstantPointContraction_eq (X : SurfaceTarget) {g : ℕ}
    {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    guardedConstantPointContraction X z beta n a =
      z.expression.pointContraction X
        (SurfacePointPullback.vertex X (constantVertex X))
        z.decoration z.labels beta n a := by
  by_cases hz : 2 ≤ z.expression.maxComponentGenus
  · rw [guardedConstantPointContraction, if_pos hz]
    exact (point_constant_eq_zero X z hz beta n a).symm
  · rw [guardedConstantPointContraction, if_neg hz]
    exact GluingExpression.scalarPointContraction_eq _ _ _ _ _ _ _ _

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.L24Relation

set_option maxRecDepth 20000

/-- The complete original L24 weighted sum, with only the justified early
higher-genus guard and the existing scalar zero-product pruning. -/
def pointConstantGuarded (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  (cotangentRelation.map fun t ↦ t.1 *
    SurfaceGenusTwo.guardedConstantPointContraction X t.2 beta n a).sum

/-- All original L24 coefficients and counted markings are preserved. -/
theorem pointConstantGuarded_eq (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantGuarded X n beta a = pointConstant X n beta a := by
  simp only [pointConstantGuarded, pointConstant,
    SurfaceGenusTwo.guardedConstantPointContraction_eq]

/-- The guarded evaluator is the constant of the entire normalized equation,
with every signed calibration tail kept in the original equality. -/
theorem pointConstantGuarded_eq_normalized (X : SurfaceTarget) (n : ℕ)
    (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantGuarded X n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) :=
  (pointConstantGuarded_eq X n beta a).trans (pointConstant_eq_normalized X n beta a)

end AxiomaticGW.L24Relation
