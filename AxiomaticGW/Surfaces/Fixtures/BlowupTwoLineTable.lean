/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCompleteness
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHConstant
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLinePrimary

/-!
# The complete energy-one grid on the two-point blowup

The four effective classes are 0, E₁, E₂ and L = H − E₁ − E₂. All five
families at L reduce to the same lower-genus scalar. The original bounded
checker therefore accepts the boundary values extended by zero precisely
when the shifted lower-genus L24 constant is 7/2880.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineTable
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupBoundedCertificate BlowupTwoLineBP

private abbrev X := SurfaceTarget.blowupTwo

/-- Extend the known plane-degree-zero boundary by a common value at positive plane degree. -/
def candidate (value : ℚ) (s : State .blowupTwo) : ℚ :=
  if SurfaceTarget.blowupTwo.planeDegree s.1 = 0 then
    SurfaceGenusTwoBlowupBoundary.value s.1 s.2
  else value

/-- Four effective classes times five distinct canonical families, including nominal P₀. -/
theorem states_length : (states .blowupTwo 1).length = 20 := by decide +kernel

/-- The original full-row checker on all twenty states has exactly one free candidate scalar,
determined by the complete lower-genus L24 sum. -/
theorem accepted_iff (v : ℚ) :
    checkTable (X := .blowupTwo) 0 1 (candidate v) = true ↔
      v = (∑ j, BlowupTwoLineH.weighted j) - 7 / 2880 := by
  rw [checkTable_iff, ← BlowupTwoLineH.constant_eq_sum, ← BlowupTwoLineH.value_eq_constant_sub]
  have hL : X.planeDegree line ≠ 0 := by decide +kernel
  constructor
  · intro h
    have he := h (line, .hyperplane) (by decide +kernel)
    simpa only [candidate, if_neg hL] using he
  · rintro rfl ⟨beta, f⟩ he
    by_cases hd : X.planeDegree beta = 0
    · rw [candidate, if_pos hd]
      exact (SurfaceGenusTwoBlowupRecursion.values_boundary 0 (beta, f) hd).symm
    · have h : (classes X 1).all (fun c ↦ decide (X.planeDegree c = 0 ∨ c = line)) = true := by
        decide +kernel
      have hc := List.all_eq_true.mp h beta ((mem_classes X 1 beta).mpr he)
      obtain rfl := (of_decide_eq_true hc).resolve_left hd
      rw [candidate, if_neg hL]
      exact (family_eq_hyperplane f).symm

/-- The boundary table with zero strict-line entries passes exactly at the stated original sum. -/
theorem zero_iff : checkTable (X := .blowupTwo) 0 1 (candidate 0) = true ↔
    (∑ j, BlowupTwoLineH.weighted j) = 7 / 2880 := by
  rw [accepted_iff]
  constructor <;> intro h <;> linarith only [h]

end AxiomaticGW.BlowupTwoLineTable
