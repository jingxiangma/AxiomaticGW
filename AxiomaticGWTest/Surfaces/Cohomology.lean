/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.Cohomology

/-! # Surface intersection regressions

These calculations use the ring and trace APIs as downstream clients do.
They check the signs on the fibre and strict-transform classes, and ensure
that the normalized point class is nonzero.
-/

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces

open AxiomaticGW SurfaceCohomology

example : point 0 ≠ 0 := by
  intro h
  have hc := congrArg (counit 0) h
  rw [counit_point, map_zero] at hc
  exact one_ne_zero hc

/-- The fibre of the first Hirzebruch surface has square zero. -/
example : (hyperplane 1 - exceptional 1 0) ^ 2 = 0 := by
  rw [sub_sq, pow_two (hyperplane 1), hyperplane_mul_hyperplane,
    pow_two (exceptional 1 0), exceptional_mul_exceptional,
    if_pos rfl]
  rw [mul_assoc, hyperplane_mul_exceptional, mul_zero, sub_zero, add_neg_cancel]

/-- The line through two blown-up points is a minus-one class. -/
example : (hyperplane 2 - exceptional 2 0 - exceptional 2 1) ^ 2 = -point 2 := by
  ring_nf
  simp only [pow_two, hyperplane_mul_hyperplane, hyperplane_mul_exceptional,
    exceptional_mul_exceptional, Fin.isValue, zero_ne_one, ↓reduceIte]
  ring

/-- The actual trace pairs each exceptional class with value minus one. -/
example (r : ℕ) (i : Fin r) :
    (frobenius r).pairing.form (exceptional r i) (exceptional r i) = -1 := by
  rw [CommFrobeniusAlgebra.pairing_apply, exceptional_mul_exceptional, if_pos rfl]
  change counit r (-point r) = -1
  rw [map_neg, counit_point]

end AxiomaticGWTest.Surfaces
