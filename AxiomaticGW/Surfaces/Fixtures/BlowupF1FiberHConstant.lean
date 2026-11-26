/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1WeightedAssembly.CheckedTable
public import AxiomaticGW.Surfaces.GenusTwoBlowupScalar

/-!
# The first F1 hyperplane row in the reconstruction API

The target class is the fiber F, with effective coordinates (E,F) = (0,1).
Its shifted L24 source is E+F, with one added point and labels H,E,E,E.
The complete checked contraction gives the lower-genus constant 1/288.
The requested genus-two descendant tau_1(H) has two primary point insertions;
its coefficient in the same row is minus one. Other genus-two terms remain.
These statements identify the constant and pivot, not the value of the invariant.
-/

@[expose] public section

namespace AxiomaticGW.BlowupF1FiberHConstant
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

/-- The scalar reconstruction uses the complete checked constant at the shifted source. -/
theorem constant_eq :
    SurfaceGenusTwoBlowupScalar.constant (X := .hirzebruchOne) 0
      (![0, 1], .hyperplane) = (1 / 288 : ℚ) := by
  have he : SurfaceTarget.hirzebruchOne.effective.energy ![0, 1] = 2 := by decide +kernel
  have hs : (![0, 1] : SurfaceTarget.hirzebruchOne.Curve) +
      SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = ![1, 1] := by
    funext k
    fin_cases k <;> rfl
  simp only [SurfaceGenusTwoBlowupScalar.constant, he, hs, Nat.reduceSub]
  exact BlowupF1WeightedAssembly.pointConstantGuarded_eq

/-- The constant is the zero valuation of the unchanged complete reconstruction row. -/
theorem row_zero_valuation :
    RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (SurfaceGenusTwoBlowupRecursion.row (X := .hirzebruchOne) 0
        (![0, 1], .hyperplane)) = (1 / 288 : ℚ) := by
  rw [← SurfaceGenusTwoBlowupScalar.constant_eq, constant_eq]

/-- The requested fiber descendant has the minus-one coefficient in that same row. -/
theorem singleton_coefficient :
    SurfaceGenusTwoBlowupScalar.singletonCoefficient (X := .hirzebruchOne) 0
      (![0, 1], .hyperplane) (.inr (Family.hyperplane.query ![0, 1])) = -1 := by
  rw [SurfaceGenusTwoBlowupScalar.singletonCoefficient_eq]
  exact SurfaceGenusTwoBlowupHContributions.row_coefficient_eq_neg_one
    .hirzebruchOne 0 ![0, 1] (by decide +kernel)

end AxiomaticGW.BlowupF1FiberHConstant
