/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowGenusPointCache
public import AxiomaticGW.Surfaces.GenusTwoL24ConstantGuard

/-!
# Reusing primary point functions in the complete scalar L24 constant

The supplied point functions enter only through the proved-equal low-genus
ancestor recursion. The existing dimension guard, signed point pullbacks,
higher-genus zero branch, all 721 held decorated terms and every coefficient
are preserved. Missing primary table entries must use an equal fallback;
no finite range, candidate invariant or numerical seed is built into this API.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo

/-- Keep the original constant vertex's guards and replace only its primary point backend. -/
def constantVertexWithPoints (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) :
    SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    if g ≤ 1 then
      let q := SurfaceAncestorKey.ofLabels g S h beta k a
      if q.DimensionCompatible then SurfaceLowGenusPointCache.componentValue X v₀ v₁ q else 0
    else 0

/-- Every original dimension-compatible and incompatible terminal has the same value. -/
theorem constantVertexWithPoints_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X) :
    constantVertexWithPoints X v₀ v₁ = constantVertex X := by
  funext g S inst h beta k a
  simp only [constantVertexWithPoints, constantVertex,
    SurfaceLowGenusPointCache.componentValue_eq X v₀ v₁ h₀ h₁]

/-- The original scalar point contraction with the same justified higher-genus guard. -/
def guardedConstantPointContractionWithPoints (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (z : GluingExpression.CotangentTerm g S)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  if 2 ≤ z.expression.maxComponentGenus then 0 else
    z.expression.scalarPointContraction X
      (SurfacePointPullback.vertex X (constantVertexWithPoints X v₀ v₁))
      z.decoration z.labels beta n a

/-- All full class splits, inverse weights and signed added-point tails remain intact. -/
theorem guardedConstantPointContractionWithPoints_eq (X : SurfaceTarget)
    (v₀ v₁ : X.Curve → ℚ) (h₀ : v₀ = SurfaceGenusZero.pointValue X)
    (h₁ : v₁ = SurfaceGenusOne.pointValue X) {g : ℕ} {S : Type} [Fintype S]
    (z : GluingExpression.CotangentTerm g S) (beta : X.Curve) (n : ℕ)
    (a : S → SurfaceBasisLabel X) :
    guardedConstantPointContractionWithPoints X v₀ v₁ z beta n a =
      guardedConstantPointContraction X z beta n a := by
  rw [guardedConstantPointContractionWithPoints, constantVertexWithPoints_eq X v₀ v₁ h₀ h₁]
  rfl

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.L24Relation

/-- Complete guarded L24 sum, reusing only proved-equal lower-genus primary functions. -/
def pointConstantWithPoints (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) (n : ℕ)
    (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) : ℚ :=
  (cotangentRelation.map fun t ↦ t.1 *
    SurfaceGenusTwo.guardedConstantPointContractionWithPoints X v₀ v₁ t.2 beta n a).sum

/-- No held term or marking count is discarded by primary table reuse. -/
theorem pointConstantWithPoints_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPoints X v₀ v₁ n beta a = pointConstantGuarded X n beta a := by
  simp only [pointConstantWithPoints, pointConstantGuarded,
    SurfaceGenusTwo.guardedConstantPointContractionWithPoints_eq X v₀ v₁ h₀ h₁]

/-- The reused backend also agrees directly with the complete original scalar constant. -/
theorem pointConstantWithPoints_eq_original (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPoints X v₀ v₁ n beta a = pointConstant X n beta a :=
  (pointConstantWithPoints_eq X v₀ v₁ h₀ h₁ n beta a).trans
    (pointConstantGuarded_eq X n beta a)

/-- The reused backend computes the constant of the entire normalized row. -/
theorem pointConstantWithPoints_eq_normalized (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (h₀ : v₀ = SurfaceGenusZero.pointValue X) (h₁ : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X) :
    pointConstantWithPoints X v₀ v₁ n beta a = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (normalizedGenusTwoTerms X n beta 0 (SurfaceGenusZero.pointLabels a n)) :=
  (pointConstantWithPoints_eq X v₀ v₁ h₀ h₁ n beta a).trans
    (pointConstantGuarded_eq_normalized X n beta a)

end AxiomaticGW.L24Relation
