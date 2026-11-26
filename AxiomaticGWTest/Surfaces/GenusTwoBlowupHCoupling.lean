/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupHCoupling

/-!
# Consumers of full-row hyperplane support

The actual positive-plane equal-measure couplings exposed by the order tests
vanish in the complete original equation. Arbitrary-class consumers also check
that nonzero collected H coefficients are self dependencies or strictly earlier.
-/

@[expose] public section

namespace AxiomaticGWTest.SurfaceGenusTwoBlowupHCoupling
open AxiomaticGW SurfaceGenusTwoBlowupHPivots SurfaceGenusTwoBlowupHCoupling

/-- E₁ + L cannot couple to E₂ + L in the shifted E₁ row at equal measure. -/
theorem first_shift_competing_class :
    RationalTerms.coefficient (row .blowupTwo 0 ![0, 1, 1])
      {hColumn .blowupTwo ![1, 0, 1]} = 0 :=
  same_planeDegree_and_energy_coefficient_eq_zero .blowupTwo 0
    (by decide +kernel) (delta := ![0, 1, 0])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The mirrored E₂ shift also retains and cancels the distinct other class. -/
theorem second_shift_competing_class :
    RationalTerms.coefficient (row .blowupTwo 1 ![1, 0, 1])
      {hColumn .blowupTwo ![0, 1, 1]} = 0 :=
  same_planeDegree_and_energy_coefficient_eq_zero .blowupTwo 1
    (by decide +kernel) (delta := ![1, 0, 0])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- No arbitrary full-class H dependency of equal measure survives except itself. -/
theorem exact_class_retained (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve) (hp : 0 < X.effective.energy beta)
    (hd : X.planeDegree gamma = X.planeDegree beta)
    (he : X.effective.energy gamma = X.effective.energy beta)
    (hc : RationalTerms.coefficient (row X i beta) {hColumn X gamma} ≠ 0) :
    gamma = beta :=
  hyperplane_coefficient_nonzero_same_measure X i beta gamma hp hd he hc

/-- The support result uses the actual original row and requires no support oracle. -/
theorem original_row_support (X : SurfaceTarget) (i : Fin X.blowups)
    (beta gamma : X.Curve) (hp : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient (row X i beta) {hColumn X gamma} ≠ 0) :
    gamma = beta ∨ SurfaceGenusTwoBlowupOrder.Earlier X
      (gamma, .hyperplane) (beta, .hyperplane) :=
  hyperplane_coefficient_support X i beta gamma hp hc

end AxiomaticGWTest.SurfaceGenusTwoBlowupHCoupling
