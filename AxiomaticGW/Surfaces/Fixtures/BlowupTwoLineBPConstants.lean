/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPrimaryConstantSymmetry
public import AxiomaticGW.Surfaces.GenusTwoBlowupPointCache
public import AxiomaticGW.Surfaces.PointBenchmarkCache

/-!
# BP constants at the strict transform of the line through both blowups

The point row and both exceptional rows use the class L = H − E₁ − E₂
with no extra points. The primary row with pivot index zero uses one extra
point at L + E₁ and the four prescribed ordered divisor triples. The primary
point backends agree with the original genus-zero and genus-one recursions.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineBP
open BelorousskiPandharipande SurfacePointBenchmarkCache

/-- The effective generator corresponding to the strict transform H − E₁ − E₂. -/
abbrev line : SurfaceTarget.blowupTwo.Curve := ![0, 0, 1]

private abbrev X := SurfaceTarget.blowupTwo

-- Run each finite graph calculation separately to bound memory.
set_option Elab.async false
set_option maxRecDepth 20000

private theorem energy_line : X.effective.energy line = 1 := by decide +kernel

private theorem triple_const (a : SurfaceBasisLabel X) :
    (![a, a, a] : Fin 3 → _) = fun _ ↦ a := by
  funext i
  fin_cases i <;> rfl

private theorem point_request : lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
    0 line (fun _ ↦ .hyperplane) = 1 / 240 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

private theorem exceptional_request (j : Fin 2) :
    lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
      0 line (fun _ ↦ .exceptional j) = 1 / 240 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  fin_cases j <;> decide +kernel

/-- Lower-genus contribution of the HHH equation for the point descendant at L. -/
theorem point_constant : SurfaceGenusTwoBlowupScalar.constant 0 (line, .point) = 1 / 240 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (line, .point)
    (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  simpa only [SurfaceGenusTwoBlowupPointCache.constant, energy_line, Nat.sub_self, triple_const]
    using point_request

/-- The two distinct all-exceptional triples contribute the same constant at L. -/
theorem exceptional_constant (j : Fin 2) :
    SurfaceGenusTwoBlowupScalar.constant 0 (line, .exceptional j) = 1 / 240 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (line, .exceptional j)
    (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  simpa only [SurfaceGenusTwoBlowupPointCache.constant, energy_line, Nat.sub_self, triple_const]
    using exceptional_request j

private abbrev shifted : X.Curve := ![1, 0, 1]

private theorem shifted_ehh : lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
    1 shifted ![.exceptional 0, .hyperplane, .hyperplane] = 0 := by
  rw [lowerPointConstantWithPrimary_eq_primaryGraphSum]
  decide +kernel

private theorem shifted_eeh : lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
    1 shifted ![.exceptional 0, .exceptional 0, .hyperplane] = 0 := by
  rw [lowerPointConstantWithPrimary_eq_primaryGraphSum]
  decide +kernel

private theorem shifted_eee : lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
    1 shifted (fun _ ↦ .exceptional 0) = 0 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

private theorem shifted_hhh : lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
    1 shifted (fun _ ↦ .hyperplane) = 1 / 120 := by
  rw [lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  decide +kernel

/-- The four original shifted triples give −1/360 in the selected primary row. -/
theorem primary_constant : SurfaceGenusTwoBlowupScalar.constant 0 (line, .primary) = -1 / 360 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (line, .primary)
    (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  have hd : X.planeDegree line = 1 := by decide +kernel
  have hs : line + X.exceptionalCurve 0 = shifted := by decide +kernel
  simp only [SurfaceGenusTwoBlowupPointCache.constant, energy_line, hd, hs, triple_const,
    shifted_ehh, shifted_eeh, shifted_eee, shifted_hhh]
  norm_num

end AxiomaticGW.BlowupTwoLineBP
