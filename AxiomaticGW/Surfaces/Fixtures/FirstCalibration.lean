/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.TwoPointCalibration

/-!
# Complete first calibration coefficients on the three surfaces

These sparse matrices describe the coefficient of `z^-1` at zero primary
deformation. The finite kernel check covers every full class of energy at
most three, including every zero matrix. The uniform primary dimension
bound proves vanishing at every higher energy. Thus the result covers all
curve classes, not just the energy-twelve benchmark window.

The geometric consumer is `SurfaceDescendant.firstCalibrationMatrix_eq`,
which derives the entries from the original WDVV inputs and finite seeds.
No new numerical seed or symplecticity hypothesis is added.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceFirstCalibration

/-- The line-class coefficient sends the point class to the unit. -/
def lineMatrix (X : SurfaceTarget) : Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  fun row col ↦ if row = .unit ∧ col = .point then 1 else 0

/-- An exceptional curve retains its negative self-intersection in the raised matrix. -/
def exceptionalMatrix (X : SurfaceTarget) (i : Fin X.blowups) :
    Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  fun row col ↦ if row = .exceptional i ∧ col = .exceptional i then -1 else 0

/-- The fiber `H - E_i` contributes its two symmetric paired divisor/point values. -/
def fiberMatrix (X : SurfaceTarget) (i : Fin X.blowups) :
    Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ :=
  fun row col ↦
    if row = .unit ∧ (col = .hyperplane ∨ col = .exceptional i) then 1 else
    if row = .hyperplane ∧ col = .point then 1 else
    if row = .exceptional i ∧ col = .point then -1 else 0

/-- The strict line `H - E_1 - E_2` has intersection one with each divisor basis vector. -/
def strictLineMatrix :
    Matrix (SurfaceBasisLabel .blowupTwo) (SurfaceBasisLabel .blowupTwo) ℚ :=
  fun row col ↦ if row.codimension = 1 ∧ col.codimension = 1 then row.inverseWeight else 0

/-- Ten nonzero full-class matrices; every other class has the zero first coefficient. -/
def values : (X : SurfaceTarget) → X.Curve →
    Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ
  | X, beta => if X.effective.energy beta ≤ 3 then
      match X with
      | .plane => if beta = ![1] then lineMatrix .plane else 0
      | .hirzebruchOne =>
          if beta = ![1,0] then exceptionalMatrix .hirzebruchOne 0 else
          if beta = ![0,1] then fiberMatrix .hirzebruchOne 0 else
          if beta = ![1,1] then lineMatrix .hirzebruchOne else 0
      | .blowupTwo =>
          if beta = ![1,0,0] then exceptionalMatrix .blowupTwo 0 else
          if beta = ![0,1,0] then exceptionalMatrix .blowupTwo 1 else
          if beta = ![0,0,1] then strictLineMatrix else
          if beta = ![0,1,1] then fiberMatrix .blowupTwo 0 else
          if beta = ![1,0,1] then fiberMatrix .blowupTwo 1 else
          if beta = ![1,1,1] then lineMatrix .blowupTwo else 0
    else 0

/-- The finite check retains every class and every signed matrix entry through energy three. -/
theorem checked (X : SurfaceTarget) :
    ∀ beta ∈ X.bounded 3, values X beta = SurfaceDescendant.firstCalibrationMatrix X beta := by
  cases X <;> decide +kernel

/-- The sparse table agrees with primary reconstruction at every full curve class. -/
theorem values_eq (X : SurfaceTarget) (beta : X.Curve) :
    values X beta = SurfaceDescendant.firstCalibrationMatrix X beta := by
  by_cases hb : X.effective.energy beta ≤ 3
  · apply checked X beta
    rw [X.bounded_eq]
    exact (X.effective.mem_bounded 3 beta).mpr hb
  · rw [SurfaceDescendant.firstCalibrationMatrix_eq_zero_of_three_lt X beta
      (Nat.lt_of_not_ge hb)]
    cases X <;> simp only [values, if_neg hb]

end AxiomaticGW.SurfaceFirstCalibration
