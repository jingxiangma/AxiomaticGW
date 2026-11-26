/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneStep
public import AxiomaticGW.Surfaces.GenusZeroRecursion

/-!
# Terminating primary genus-one point reconstruction

The original four-hyperplane Getzler equation has coefficient minus nine
outside the energy-at-most-one initial sector. Genus-zero dependencies use
the existing reconstruction, including at the original energy; only genus-one
dependencies recurse, with strictly decreasing energy. The initial values
are zero, whose derivation from the original finite seeds is separate.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

open SurfacePolynomialReduction SurfaceLowGenus
open SurfaceGenusZero (variableCurve pointLabels)

/-- The finite initial sector preceding the uniform elliptic recursion. -/
def IsInitial (X : SurfaceTarget) (beta : X.Curve) : Prop :=
  X.effective.energy beta ≤ 1

instance (X : SurfaceTarget) (beta : X.Curve) : Decidable (IsInitial X beta) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The complete original Getzler equation, with every ordered point placement. -/
def reconstructionTerms (X : SurfaceTarget) (beta : X.Curve) : RationalTerms (Variable X) :=
  GetzlerGraphs.primaryTerms X (X.effective.energy beta - 2) beta 0
    (pointLabels (GetzlerGraphs.reconstructionLabels X) (X.effective.energy beta - 2))

/-- Exact coefficient of the requested elliptic point query. -/
def reconstructionCoefficient (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  RationalTerms.coefficient (reconstructionTerms X beta) {pointVariable X 1 beta}

/-- Remove all occurrences of precisely the requested elliptic singleton. -/
def reconstructionRemainder (X : SurfaceTarget) (beta : X.Curve) :
    RationalTerms (Variable X) := lowerTerms X beta (reconstructionTerms X beta)

/-- Nonvanishing is a theorem about the full graph equation, not an input. -/
theorem reconstructionCoefficient_eq (X : SurfaceTarget) (beta : X.Curve)
    (h : ¬IsInitial X beta) : reconstructionCoefficient X beta = -9 :=
  GetzlerGraphs.primaryTerms_reconstruction_coefficient X beta (by
    unfold IsInitial at h
    omega)

theorem reconstructionCoefficient_ne_zero (X : SurfaceTarget) (beta : X.Curve)
    (h : ¬IsInitial X beta) : reconstructionCoefficient X beta ≠ 0 := by
  rw [reconstructionCoefficient_eq X beta h]
  norm_num

/-- Genus-zero dependencies may have the original energy; genus-one dependencies cannot. -/
theorem reconstructionRemainder_dependencies (X : SurfaceTarget) (beta : X.Curve)
    (t : ℚ × Multiset (Variable X)) (ht : t ∈ reconstructionRemainder X beta)
    (v : Variable X) (hv : v ∈ t.2) :
    ∃ g gamma, gamma ≠ 0 ∧ v = pointVariable X g gamma ∧ g ≤ 1 ∧
      (g = 0 ∨ X.effective.energy gamma < X.effective.energy beta) :=
  getzler_lowerTerms_dependencies X (X.effective.energy beta - 2) beta
    (pointLabels (GetzlerGraphs.reconstructionLabels X) (X.effective.energy beta - 2)) t ht v hv

/-- Separate the already reconstructed rational values from the elliptic candidates.
The support theorem proves that actual variables have genus zero or one. -/
def pointValuation {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ) (u : Variable X) : ℚ :=
  if variableGenus u = 0 then v₀ (variableCurve u) else v₁ (variableCurve u)

theorem pointValuation_point {X : SurfaceTarget} (v₀ v₁ : X.Curve → ℚ)
    (g : ℕ) (beta : X.Curve) :
    pointValuation v₀ v₁ (pointVariable X g beta) = if g = 0 then v₀ beta else v₁ beta := rfl

/-- Exact elliptic computation. The guard makes the valuation total on arbitrary
variables; support proves it never discards a dependency of the actual remainder. -/
def pointValue (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  if IsInitial X beta then 0 else
    -RationalTerms.eval (fun v ↦
      if variableGenus v = 0 then SurfaceGenusZero.pointValue X (variableCurve v) else
        if _hlt : X.effective.energy (variableCurve v) < X.effective.energy beta then
          pointValue X (variableCurve v) else 0) (reconstructionRemainder X beta) /
      reconstructionCoefficient X beta
termination_by X.effective.energy beta
decreasing_by exact _hlt

/-- Initial elliptic point values, including the auxiliary zero-class zero-point value. -/
theorem pointValue_initial (X : SurfaceTarget) (beta : X.Curve) (h : IsInitial X beta) :
    pointValue X beta = 0 := by
  rw [pointValue, if_pos h]

/-- The guard disappears on the actual graph polynomial by strict decrease. -/
theorem pointValue_step (X : SurfaceTarget) (beta : X.Curve) (h : ¬IsInitial X beta) :
    pointValue X beta =
      -RationalTerms.eval (pointValuation (SurfaceGenusZero.pointValue X) (pointValue X))
        (reconstructionRemainder X beta) / reconstructionCoefficient X beta := by
  rw [pointValue, if_neg h]
  congr 2
  apply RationalTerms.eval_congr
  intro t ht v hv
  obtain ⟨g, gamma, _, rfl, _, hlt⟩ := reconstructionRemainder_dependencies X beta t ht v hv
  change (if g = 0 then SurfaceGenusZero.pointValue X gamma else
      if _h : X.effective.energy gamma < X.effective.energy beta then pointValue X gamma else 0) =
    if g = 0 then SurfaceGenusZero.pointValue X gamma else pointValue X gamma
  by_cases hg : g = 0
  · simp only [if_pos hg]
  · simp only [if_neg hg, dif_pos (hlt.resolve_left hg)]

/-- With the existing genus-zero reconstruction fixed, the initial sector and
actual Getzler equations determine the elliptic point function uniquely. -/
theorem eq_pointValue_of_equations (X : SurfaceTarget) (v : X.Curve → ℚ)
    (hinitial : ∀ beta, IsInitial X beta → v beta = 0)
    (hstep : ∀ beta, ¬IsInitial X beta → v beta =
      -RationalTerms.eval (pointValuation (SurfaceGenusZero.pointValue X) v)
        (reconstructionRemainder X beta) / reconstructionCoefficient X beta)
    (beta : X.Curve) : v beta = pointValue X beta := by
  induction beta using (measure (fun b : X.Curve ↦ X.effective.energy b)).wf.induction with
  | h beta ih =>
    by_cases hinit : IsInitial X beta
    · rw [hinitial beta hinit, pointValue_initial X beta hinit]
    · rw [hstep beta hinit, pointValue_step X beta hinit]
      congr 2
      apply RationalTerms.eval_congr
      intro t ht u hu
      obtain ⟨g, gamma, _, rfl, _, hlt⟩ := reconstructionRemainder_dependencies X beta t ht u hu
      simp only [pointValuation_point]
      by_cases hg : g = 0
      · simp only [if_pos hg]
      · simp only [if_neg hg]
        exact ih gamma (hlt.resolve_left hg)

/-- Reconstruct primary genus-one basis multisets. Degree-zero values use the
existing elliptic divisor constants; positive classes retain signed divisor factors. -/
def primaryValue (X : SurfaceTarget) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if beta = 0 then SurfacePrimary.genusOneZeroValue m else
    if m.count .point = X.effective.energy beta then
      (m.map (SurfaceBasisLabel.primaryFactor beta)).prod * pointValue X beta
    else 0

end AxiomaticGW.SurfaceGenusOne
