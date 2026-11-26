/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.FirstCalibrationReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.TwoPointCalibration
open AxiomaticGW SurfaceDescendant SurfaceFirstCalibration

/-- The plane line sends the point class to the unit, with no other entries. -/
example : values .plane ![1] = lineMatrix .plane := by decide +kernel

/-- All higher plane classes have zero first coefficient, including beyond the benchmark bound. -/
example : values .plane ![100] = 0 := by decide +kernel

/-- Raising the exceptional two-point index retains its minus sign. -/
example : values .hirzebruchOne ![1,0] (.exceptional 0) (.exceptional 0) = -1 := by
  decide +kernel

/-- The two directions of the fiber coefficient retain their respective metric signs. -/
example : values .hirzebruchOne ![0,1] .unit (.exceptional 0) = 1 ∧
    values .hirzebruchOne ![0,1] (.exceptional 0) .point = -1 := by decide +kernel

/-- Equal-energy exceptional curves are distinct full-class requests. -/
example : values .blowupTwo ![1,0,0] (.exceptional 0) (.exceptional 0) = -1 ∧
    values .blowupTwo ![0,1,0] (.exceptional 0) (.exceptional 0) = 0 := by decide +kernel

/-- The strict line includes mixed exceptional entries in its full divisor block. -/
example : values .blowupTwo ![0,0,1] .hyperplane (.exceptional 1) = 1 ∧
    values .blowupTwo ![0,0,1] (.exceptional 0) (.exceptional 1) = -1 := by decide +kernel

/-- Distinct ruling classes use the corresponding exceptional coordinate. -/
example : values .blowupTwo ![0,1,1] .unit (.exceptional 0) = 1 ∧
    values .blowupTwo ![1,0,1] .unit (.exceptional 0) = 0 := by decide +kernel

/-- The line class on the two-point blowup retains all three effective coordinates. -/
example : values .blowupTwo ![1,1,1] = lineMatrix .blowupTwo := by decide +kernel

/-- Degree-zero two-point invariants supply no inverse-loop coefficient. -/
example : values .plane 0 = 0 ∧ values .hirzebruchOne 0 = 0 ∧ values .blowupTwo 0 = 0 := by
  decide +kernel

/-- Reducible or multiple exceptional classes are retained as checked zero matrices. -/
example : values .blowupTwo ![1,1,0] = 0 ∧ values .blowupTwo ![0,0,2] = 0 := by
  decide +kernel

/-- Native GKM values are replayed at the actual incoming full classes and labels. -/
example (i row col) : GKM.FirstCalibrationReplay.TwoBlowups.entries i row col =
    firstCalibrationMatrix .blowupTwo (GKM.FirstCalibrationReplay.TwoBlowups.classes i)
      (GKM.FirstCalibrationReplay.TwoBlowups.labels row)
      (GKM.FirstCalibrationReplay.TwoBlowups.labels col) :=
  GKM.FirstCalibrationReplay.TwoBlowups.reconstructed i row col

/-- The complete first-coefficient claim holds at arbitrary energy. -/
example (X : SurfaceTarget) (beta : X.Curve) : values X beta = firstCalibrationMatrix X beta :=
  values_eq X beta

section GeometricConsumers
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)

/-- Power one uses primary two-point invariants; it does not use a psi-one invariant. -/
example (beta : X.Curve) (x y : SurfaceCohomology X.blowups) :
    Omega.pairing.form x (U.calibrationCoefficient 1 beta y) =
      U.invariant 0 (Fin 2) beta ![0,0] ![x,y] := U.calibrationCoefficient_pairing 0 beta x y

/-- Primary relabelling supplies the first-order symmetry condition. -/
example (beta : X.Curve) (x y : SurfaceCohomology X.blowups) :
    Omega.pairing.form x (U.calibrationCoefficient 1 beta y) =
      Omega.pairing.form (U.calibrationCoefficient 1 beta x) y :=
  U.calibrationCoefficient_one_selfAdjoint beta x y

/-- The identity convention is separate from the auxiliary zero two-point invariant. -/
example : U.calibrationCoefficient 0 0 = LinearMap.id ∧
    U.calibrationCoefficient 1 0 = 0 :=
  ⟨U.calibrationCoefficient_constant, U.calibrationCoefficient_zero_class 0⟩

/-- No positive curve class enters the constant-in-loop-degree coefficient. -/
example (beta : X.Curve) (hb : beta ≠ 0) : U.calibrationCoefficient 0 beta = 0 :=
  U.calibrationCoefficient_zero_power beta hb

/-- Each curve class has a proved finite inverse-loop support. -/
example (beta : X.Curve) :
    U.calibrationCoefficient (X.effective.energy beta + 3) beta = 0 := by
  apply calibrationCoefficient_eq_zero_of_high_power U T (X.effective.energy beta + 2) beta
  omega

/-- The existing comparison consumes paired geometric identification without an operator oracle. -/
example {P : PsiClasses C} (K : StabilizationBoundaryComparison P M)
    (h : K.TwoPointCompatible U) (m : ℕ) (beta : X.Curve) :
    K.twoPointTailCoefficient m beta = U.calibrationCoefficient m beta :=
  K.tailCoefficient_eq U h m beta

/-- A linear main-component contribution sews directly to the actual tail state. -/
example (m : ℕ) (beta : X.Curve) (ell : Module.Dual ℚ (SurfaceCohomology X.blowups))
    (y : SurfaceCohomology X.blowups) :
    TensorProduct.lift (((LinearMap.mul ℚ ℚ).comp ell).compl₂
        ((SymmetricPerfectPairing.finTwoToBilin (U.invariantMap 0 (Fin 2) beta ![0,m])).flip y))
      Omega.pairing.copairing = ell (U.calibrationCoefficient (m+1) beta y) :=
  U.calibrationCoefficient_contract m beta ell y

end GeometricConsumers
end AxiomaticGWTest.Surfaces.TwoPointCalibration
