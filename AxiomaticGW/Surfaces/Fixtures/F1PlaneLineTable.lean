/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineL24
public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineBP
public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLinePrimaryValue
public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCompleteness

/-! # The energy-three genus-two F₁ grid expressed by one original L24 residual

The BP and L24 equations at the new full class E+F express H and P by one
signed residual. N and K vanish. The descendant incidence argument in
`F1PlaneLineL24Replay` evaluates the residual and certifies the numerical table.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLine
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundedCertificate

/-- Signed value from the 815-position shifted source and its two class-zero divisors. -/
def residual : ℚ := (∑ j, weighted j) -
  divisorCoefficient .hyperplane / 960 - divisorCoefficient (.exceptional 0) / 2880

/-- The bounded row candidate retaining the signed L24 scalar. -/
def candidate (h : ℚ) (s : State X) : ℚ :=
  if s.1 = line then
    match s.2 with
    | .hyperplane | .point => h
    | .primary | .exceptional _ => 0
  else BlowupF1FiberHReduction.boundary s

/-- The complete 24-state candidate agrees with the canonical recursion exactly at the L24 value. -/
theorem accepted_iff (h : ℚ) : checkTable (X := X) 0 3 (candidate h) = true ↔ h = residual := by
  rw [checkTable_iff]
  constructor
  · intro hc
    have hh := hc (line, .hyperplane) (by change X.effective.energy line ≤ 3; decide +kernel)
    exact hh.trans hyperplane_eq_frame
  · rintro rfl ⟨beta, f⟩ hb
    by_cases hc : beta = line
    · subst beta
      simp only [candidate, ite_true]
      cases f with
      | hyperplane => exact hyperplane_eq_frame.symm
      | point => exact (point_eq_hyperplane.trans hyperplane_eq_frame).symm
      | primary => exact primary_value.symm
      | exceptional i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact exceptional_value.symm
    · simp only [candidate, if_neg hc]
      by_cases hd : X.effective.energy beta ≤ 2
      · exact (BlowupF1FiberTable.values_eq (beta, f) hd).symm
      · have hz : beta 1 = 0 := by
          change X.effective.energy beta ≤ 3 at hb
          rw [BlowupF1FiberHReduction.energy_formula] at hb hd
          change beta 0 + 2 * beta 1 ≤ 3 at hb
          change ¬ (beta 0 + 2 * beta 1 ≤ 2) at hd
          by_contra hn
          have h₁ : beta 1 = 1 := by omega
          have h₂ : beta 0 = 1 := by omega
          apply hc
          funext i
          fin_cases i
          · exact h₂
          · exact h₁
        exact (SurfaceGenusTwoBlowupRecursion.values_boundary 0 (beta,f) hz).symm

/-- The unchanged finite row checker recognizes the symbolic grid unconditionally. -/
theorem accepted_exact : checkTable (X := X) 0 3 (candidate residual) = true :=
  (accepted_iff residual).mpr rfl

end AxiomaticGW.F1PlaneLine
