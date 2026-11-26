/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.SurfaceReplay
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-!
# Research surface state-space replay regressions

These examples consume the exported certificates through the actual perfect
pairing and transported product. They test cancellation in the complete
metric, the exceptional self-intersection sign, and distinct exceptional
basis states. No numerical GW invariant is claimed.
-/

namespace AxiomaticGWTest.GKM.SurfaceReplay

open AxiomaticGW AxiomaticGW.GKM EquivariantCoefficients

example : Specializes
    (((FixedPointAlgebra.algebra SurfaceReplay.Plane.accepted.eulerUnits).pairing.comap
      SurfaceReplay.Plane.accepted.equivalence).form
        (Pi.single (1 : Fin 3) 1) (Pi.single (1 : Fin 3) 1)) 1 := by
  rw [SurfaceReplay.Plane.accepted.metric_correct]
  convert SurfaceReplay.Plane.accepted.metric_specializes 1 1 using 1
  change (1 : ℚ) = tracePairing (SurfaceCohomology.counit 0)
    (SurfaceCohomology.hyperplane 0) (SurfaceCohomology.hyperplane 0)
  rw [SurfaceCohomology.tracePairing_counit_hyperplane]
  rfl

-- The localized pairing of H and point is nonzero.
-- Their ordinary degrees are not complementary, so that grading cannot be copied to this field.
example :
    ((FixedPointAlgebra.algebra SurfaceReplay.Plane.accepted.eulerUnits).pairing.comap
      SurfaceReplay.Plane.accepted.equivalence).form
        (Pi.single (1 : Fin 3) 1) (Pi.single (2 : Fin 3) 1) ≠ 0 := by
  rw [SurfaceReplay.Plane.accepted.metric_correct]
  have h : SurfaceReplay.Plane.tables.metric 1 2 = -y := by
    dsimp only [SurfaceReplay.Plane.tables, SurfaceReplay.Plane.values,
      SurfaceReplay.Plane.numerators, SurfaceReplay.Plane.denominators, Matrix.cons_val,
      Matrix.of_apply]
    norm_num only [map_mul, embed_C, embed_X_one, div_one, neg_one_mul]
    rfl
  rw [h]
  exact neg_ne_zero.mpr y_ne_zero

example : Specializes
    ((StateSpaceTransport.product SurfaceReplay.OneBlowup.accepted.equivalence
      (Pi.single (2 : Fin 4) 1) (Pi.single (2 : Fin 4) 1)) 3) (-1) := by
  rw [SurfaceReplay.OneBlowup.accepted.product_correct]
  convert SurfaceReplay.OneBlowup.accepted.products_specialize 2 2 3 using 1
  dsimp only [SurfaceFrames.OneBlowup.request, SurfaceFrames.OneBlowup.states,
    SurfaceFrames.OneBlowup.coordinates, Matrix.cons_val]
  norm_num only [SurfaceFrames.OneBlowup.request, SurfaceFrames.OneBlowup.states,
    SurfaceFrames.OneBlowup.coordinates, SurfaceCohomology.cupProduct,
    SurfaceCohomology.exceptional, SurfaceCohomology.divisorIntersection,
    Pi.single_apply, Fin.sum_univ_succ, Fintype.sum_empty, Fin.val_natCast, Fin.val_one',
    Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
    ite_true, ite_false]

example : Specializes
    ((StateSpaceTransport.product SurfaceReplay.TwoBlowups.accepted.equivalence
      (Pi.single (2 : Fin 5) 1) (Pi.single (3 : Fin 5) 1)) 4) 0 := by
  rw [SurfaceReplay.TwoBlowups.accepted.product_correct]
  convert SurfaceReplay.TwoBlowups.accepted.products_specialize 2 3 4 using 1
  dsimp only [SurfaceFrames.TwoBlowups.request, SurfaceFrames.TwoBlowups.states,
    SurfaceFrames.TwoBlowups.coordinates, Matrix.cons_val]
  norm_num only [SurfaceFrames.TwoBlowups.request, SurfaceFrames.TwoBlowups.states,
    SurfaceFrames.TwoBlowups.coordinates, SurfaceCohomology.cupProduct,
    SurfaceCohomology.exceptional, SurfaceCohomology.divisorIntersection,
    Pi.single_apply, Fin.sum_univ_succ, Fintype.sum_empty, Fin.val_natCast, Fin.val_one',
    Matrix.cons_val, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
    Fin.mk.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_succ, ite_true, ite_false]

example (value : ℚ) : ¬Specializes ((SurfaceFrames.Plane.request.euler 0)⁻¹) value := by
  change ¬Specializes ((x*y)⁻¹) value
  have hp : embed (MvPolynomial.X 0 * MvPolynomial.X 1) ≠ 0 := by
    rw [map_mul, embed_X_zero, embed_X_one]
    exact mul_ne_zero x_ne_zero y_ne_zero
  have hz : atZero (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
    simp only [map_mul, atZero, MvPolynomial.eval₂Hom_X',
      Pi.zero_apply, mul_zero]
  simpa only [map_mul, embed_X_zero, embed_X_one] using
    not_specializes_inverse (MvPolynomial.X 0 * MvPolynomial.X 1) hp hz value

end AxiomaticGWTest.GKM.SurfaceReplay
