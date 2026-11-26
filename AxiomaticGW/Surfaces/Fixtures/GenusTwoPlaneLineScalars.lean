/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoCertificate

/-!
# Exact scalars for the plane genus-two line certificate

The complete source-degree-two constants and coefficients are checked before
assembling the finite table. They are computations, not additional seeds.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoPlaneLineScalars
open BelorousskiPandharipande

private theorem constant_0 : planeShiftedConstantFast 1 0 = 1 / 10 := by decide +kernel
private theorem constant_1 : planeShiftedConstantFast 1 1 = 1 / 20 := by decide +kernel
private theorem constant_2 : planeShiftedConstantFast 1 2 = 1 / 40 := by decide +kernel

private theorem coefficient_0 : planeEarlierCoefficient 1 0 0 1 = 96 := by decide +kernel
private theorem coefficient_1 : planeEarlierCoefficient 1 1 0 1 = 48 := by decide +kernel
private theorem coefficient_2 : planeEarlierCoefficient 1 2 0 1 = 24 := by decide +kernel

/-- All three full lower-genus constants, in HHP/HPP/PPP order. -/
theorem constants (i : Fin 3) :
    planeShiftedConstantFast 1 i = (![1 / 10, 1 / 20, 1 / 40] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact constant_0
  · exact constant_1
  · exact constant_2

/-- The coefficient of the only nonzero initial value is kept in every equation. -/
theorem coefficients (i : Fin 3) :
    planeEarlierCoefficient 1 i 0 1 = (![96, 48, 24] : Fin 3 → ℚ) i := by
  fin_cases i
  · exact coefficient_0
  · exact coefficient_1
  · exact coefficient_2

end AxiomaticGW.GenusTwoPlaneLineScalars
