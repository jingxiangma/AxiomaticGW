/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCoefficientRelations

/-!
# Shifted hyperplane coefficients on the rational blowups

The L24 request has four states `H, Eᵢ, Eᵢ, Eᵢ`, source class `beta + Eᵢ`,
and `energy(beta) - 1` additional labelled points. The marking count has the
required dimension only at positive energy. Its selected column is the genus-two
descendant `tau₁(H)` with `energy(beta)` primary points at the original full class.

The coefficient is identified with the complete normalized L24 equation,
including its constants, other variables and signed ancestor corrections.
Five finite requests have coefficient minus one, checked in the kernel.
These identities neither close the other dependencies nor assert a uniform
pivot, a solved recurrence or geometric existence.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupHPivots
open SurfacePolynomialReduction

/-- The original-class hyperplane first descendant, with all its primary points. -/
def hColumn (X : SurfaceTarget) (beta : X.Curve) : Variable X :=
  .inr (SurfaceFirstDescendant.query 2 beta .hyperplane (X.effective.energy beta))

/-- The four labelled divisor states of the shifted L24 request. -/
def labels (X : SurfaceTarget) (i : Fin X.blowups) : Fin 4 → SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional i, .exceptional i, .exceptional i]

/-- Shift by the actual exceptional generator in the full effective curve monoid. -/
def sourceCurve (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) : X.Curve :=
  beta + X.exceptionalCurve i

/-- Additional labelled primary points; the dimension identity requires positive energy. -/
def pointCount (X : SurfaceTarget) (beta : X.Curve) : ℕ :=
  X.effective.energy beta - 1

/-- The complete normalized equation, retaining every constant and residual variable. -/
def row (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    RationalTerms (Variable X) :=
  L24Relation.normalizedGenusTwoTerms X (pointCount X beta) (sourceCurve X i beta) 0
    (SurfaceGenusZero.pointLabels (labels X i) (pointCount X beta))

/-- Compressed computation of just the selected coefficient in the complete row. -/
def coefficient (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) : ℚ :=
  L24Relation.pointCoefficient X (pointCount X beta) (sourceCurve X i beta)
    (labels X i) (hColumn X beta)

/-- Compression preserves the exact coefficient of the original normalized L24 equation. -/
theorem coefficient_eq_full (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    coefficient X i beta = RationalTerms.coefficient (row X i beta) {hColumn X beta} :=
  L24Relation.pointCoefficient_eq_full X (pointCount X beta) (sourceCurve X i beta)
    (labels X i) (hColumn X beta)

/-- The source shift raises anticanonical energy by precisely one. -/
theorem sourceCurve_energy (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve) :
    X.effective.energy (sourceCurve X i beta) = X.effective.energy beta + 1 := by
  rw [sourceCurve, map_add]
  congr 1
  cases X <;> fin_cases i <;> decide +kernel

/-- At positive energy the four divisor states and additional points have the
marking count required by the codimension-three L24 equation. -/
theorem pointCount_dimension (X : SurfaceTarget) (i : Fin X.blowups) (beta : X.Curve)
    (hbeta : 0 < X.effective.energy beta) :
    pointCount X beta + 2 = X.effective.energy (sourceCurve X i beta) := by
  rw [pointCount, sourceCurve_energy]
  omega

set_option maxRecDepth 20000

/-- Exceptional-class hyperplane pivot on F₁, from the complete source class `2E`. -/
theorem hirzebruchOne_exceptional : coefficient .hirzebruchOne 0 ![1, 0] = -1 := by
  rw [coefficient, L24Relation.pointCoefficient_eq]
  decide +kernel

/-- Fiber-class hyperplane pivot on F₁, from source `E + F` and one added point. -/
theorem hirzebruchOne_fiber : coefficient .hirzebruchOne 0 ![0, 1] = -1 := by
  rw [coefficient, L24Relation.pointCoefficient_eq]
  decide +kernel

/-- The E₁ column at source `2E₁` retains the exceptional intersection signs. -/
theorem blowupTwo_firstExceptional : coefficient .blowupTwo 0 ![1, 0, 0] = -1 := by
  rw [coefficient, L24Relation.pointCoefficient_eq]
  decide +kernel

/-- The E₂ column is checked at source `E₁ + E₂`, retaining the distinct full classes. -/
theorem blowupTwo_secondExceptional : coefficient .blowupTwo 0 ![0, 1, 0] = -1 := by
  rw [coefficient, L24Relation.pointCoefficient_eq]
  decide +kernel

/-- The strict-line column uses source `E₁ + L₁₂`, a different class of the same energy. -/
theorem blowupTwo_strictLine : coefficient .blowupTwo 0 ![0, 0, 1] = -1 := by
  rw [coefficient, L24Relation.pointCoefficient_eq]
  decide +kernel

end AxiomaticGW.SurfaceGenusTwoBlowupHPivots
