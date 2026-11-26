/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.EquivariantCoefficients
import Mathlib.Tactic.Ring

set_option linter.privateModule false

/-!
# Complete-sum specialization and genuine poles

An inverse character has no regular ordinary value. Cancellation of two
polar terms does give a regular complete expression. These fixtures test
the domain of specialization rather than just a polynomial substitution.
-/

namespace AxiomaticGWTest.GKM.EquivariantCoefficients

open AxiomaticGW.GKM.EquivariantCoefficients

example (value : ℚ) : ¬Specializes (x⁻¹) value :=
  not_specializes_inverse (MvPolynomial.X 0) x_ne_zero
    (by rw [atZero, MvPolynomial.eval₂Hom_X', Pi.zero_apply]) value

example : Specializes (x⁻¹ + (1 - x⁻¹)) 1 := by
  have h : x⁻¹ + (1 - x⁻¹) = embed (1 : Polynomial) := by
    rw [map_one]
    ring
  simpa only [map_one] using specializes_of_eq_polynomial 1 h

example {f : Coefficient} {a b : ℚ} (ha : Specializes f a) (hb : Specializes f b) :
    a = b := ha.unique hb

end AxiomaticGWTest.GKM.EquivariantCoefficients
