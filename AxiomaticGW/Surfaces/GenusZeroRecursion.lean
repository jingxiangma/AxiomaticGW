/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroUniform

/-!
# Terminating primary genus-zero point reconstruction

The initial sector consists of energy at most two and the line seed. All
other classes use the original WDVV request with a proved nonzero coefficient.
The recursive calls decrease anticanonical energy. The initial values are a
finite executable table; their derivation from the existing geometric inputs
and seeds is established in `GenusZeroReconstruction`.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

open SurfacePolynomialReduction

/-- The finite sector preceding the uniform WDVV recursion, including the line seed. -/
def IsInitial (X : SurfaceTarget) (beta : X.Curve) : Prop :=
  X.effective.energy beta ≤ 2 ∨ beta = X.lineCurve

instance (X : SurfaceTarget) (beta : X.Curve) : Decidable (IsInitial X beta) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Values on the initial sector. Outside that sector this function is unused.
The value at zero is the existing auxiliary zero-point convention. -/
def initialValue (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  if beta = X.lineCurve then 1 else
    match X with
    | .plane => 0
    | .hirzebruchOne => if beta = ![1, 0] ∨ beta = ![0, 1] then 1 else 0
    | .blowupTwo =>
        if SurfaceTarget.blowupTwo.effective.energy beta = 1 ∨
            beta = ![1, 0, 1] ∨ beta = ![0, 1, 1] then 1 else 0

/-- The original four states and number of added points for the selected request. -/
def reconstructionRequest (X : SurfaceTarget) (beta : X.Curve) :
    (n : ℕ) × (ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :=
  if X.effective.energy beta = 3 then
    match X with
    | .plane => ⟨0, WDVV.reconstructionLabels .plane⟩
    | .hirzebruchOne => ⟨0, WDVV.hirzebruchEnergyThreeLabels beta⟩
    | .blowupTwo => ⟨0, WDVV.blowupEnergyThreeLabels beta⟩
  else ⟨X.effective.energy beta - 4,
    pointLabels (WDVV.reconstructionLabels X) (X.effective.energy beta - 4)⟩

/-- The unchanged complete graph equation for the selected request. -/
def reconstructionTerms (X : SurfaceTarget) (beta : X.Curve) : RationalTerms (Variable X) :=
  WDVV.primaryTerms X (reconstructionRequest X beta).1 beta 0
    (reconstructionRequest X beta).2

/-- The exact leading coefficient; no recurrence coefficient is an input. -/
def reconstructionCoefficient (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  RationalTerms.coefficient (reconstructionTerms X beta) {pointVariable X beta}

/-- The full remaining polynomial after all occurrences of the leading singleton are removed. -/
def reconstructionRemainder (X : SurfaceTarget) (beta : X.Curve) :
    RationalTerms (Variable X) := lowerTerms X beta (reconstructionTerms X beta)

/-- Every class outside the initial sector has a nonzero exact leading coefficient. -/
theorem reconstructionCoefficient_ne_zero (X : SurfaceTarget) (beta : X.Curve)
    (h : ¬IsInitial X beta) : reconstructionCoefficient X beta ≠ 0 := by
  have he : ¬X.effective.energy beta ≤ 2 := fun he ↦ h (Or.inl he)
  by_cases hthree : X.effective.energy beta = 3
  · cases X with
    | plane => exact (h (Or.inr (WDVV.plane_energy_three_eq_line beta hthree))).elim
    | hirzebruchOne =>
        rw [reconstructionCoefficient, reconstructionTerms, reconstructionRequest, if_pos hthree]
        exact WDVV.primaryTerms_hirzebruch_energy_three_coefficient_ne_zero beta hthree
    | blowupTwo =>
        rw [reconstructionCoefficient, reconstructionTerms, reconstructionRequest, if_pos hthree]
        exact WDVV.primaryTerms_blowup_energy_three_coefficient_ne_zero beta hthree
  · have hfour : 4 ≤ X.effective.energy beta := by omega
    rw [reconstructionCoefficient, reconstructionTerms, reconstructionRequest.eq_def, if_neg hthree,
      WDVV.primaryTerms_reconstruction_coefficient X beta hfour]
    exact one_ne_zero

/-- The actual terms preserve the full class and contain only smaller positive point queries. -/
theorem reconstructionRemainder_dependencies (X : SurfaceTarget) (beta : X.Curve)
    (t : ℚ × Multiset (Variable X)) (ht : t ∈ reconstructionRemainder X beta)
    (v : Variable X) (hv : v ∈ t.2) :
    ∃ gamma : X.Curve, gamma ≠ 0 ∧ v = pointVariable X gamma ∧
      X.effective.energy gamma < X.effective.energy beta :=
  wdvv_lowerTerms_dependencies X (reconstructionRequest X beta).1 beta
    (reconstructionRequest X beta).2 t ht v hv

/-- Exact point-invariant computation, with recursion justified by decreasing energy.
The guard makes the valuation total on arbitrary variables; the support theorem
proves its zero branch is never used by any term of the actual remainder. -/
def pointValue (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  if IsInitial X beta then initialValue X beta else
    -RationalTerms.eval (fun v ↦
      if _hlt : X.effective.energy (variableCurve v) < X.effective.energy beta then
        pointValue X (variableCurve v) else 0) (reconstructionRemainder X beta) /
      reconstructionCoefficient X beta
termination_by X.effective.energy beta
decreasing_by exact _hlt

/-- Computation agrees with the finite table on the initial sector. -/
theorem pointValue_initial (X : SurfaceTarget) (beta : X.Curve) (h : IsInitial X beta) :
    pointValue X beta = initialValue X beta := by
  rw [pointValue, if_pos h]

/-- On every recursive branch the guard disappears by proved strict decrease. -/
theorem pointValue_step (X : SurfaceTarget) (beta : X.Curve) (h : ¬IsInitial X beta) :
    pointValue X beta =
      -RationalTerms.eval (fun v ↦ pointValue X (variableCurve v))
        (reconstructionRemainder X beta) / reconstructionCoefficient X beta := by
  rw [pointValue, if_neg h]
  congr 2
  apply RationalTerms.eval_congr
  intro t ht v hv
  obtain ⟨gamma, _, rfl, hlt⟩ := reconstructionRemainder_dependencies X beta t ht v hv
  exact dif_pos hlt

/-- Initial values and the actual decreasing equations determine the point function uniquely.
The geometric consumer proves these hypotheses from the original relation and finite seeds. -/
theorem eq_pointValue_of_equations (X : SurfaceTarget) (v : X.Curve → ℚ)
    (hinitial : ∀ beta, IsInitial X beta → v beta = initialValue X beta)
    (hstep : ∀ beta, ¬IsInitial X beta → v beta =
      -RationalTerms.eval (fun u ↦ v (variableCurve u)) (reconstructionRemainder X beta) /
        reconstructionCoefficient X beta) (beta : X.Curve) : v beta = pointValue X beta := by
  induction beta using (measure (fun b : X.Curve ↦ X.effective.energy b)).wf.induction with
  | h beta ih =>
    by_cases hinit : IsInitial X beta
    · rw [hinitial beta hinit, pointValue_initial X beta hinit]
    · rw [hstep beta hinit, pointValue_step X beta hinit]
      congr 2
      apply RationalTerms.eval_congr
      intro t ht u hu
      obtain ⟨gamma, _, rfl, hlt⟩ := reconstructionRemainder_dependencies X beta t ht u hu
      exact ih gamma hlt

/-- Reconstruct every primary basis multiset, including its degree-zero classical value.
Positive-class units and divisors use the existing signed primary factors;
the point count enforces the remaining dimension condition. -/
def primaryValue (X : SurfaceTarget) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if beta = 0 then SurfacePrimary.classicalValue m else
    if m.count .point = X.effective.energy beta - 1 then
      (m.map (SurfaceBasisLabel.primaryFactor beta)).prod * pointValue X beta
    else 0

end AxiomaticGW.SurfaceGenusZero
