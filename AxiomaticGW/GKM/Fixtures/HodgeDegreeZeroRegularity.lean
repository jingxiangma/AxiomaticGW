/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientFormula
public import Mathlib.Tactic.FieldSimp

/-!
# Complete fixed-point pole cancellation for formal Hodge polynomials

Each complete sum uses all actual incoming ordered coefficients.
Its explicit lift has polynomial torus-character coefficients, and only that
lift is evaluated at zero. The lambda symbols remain formal indeterminates.
No field-to-QQ evaluation, geometric Hodge product, Mumford relation, GW class
identification, localization theorem or CohFT law is asserted.
-/

@[expose] public section

set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeDegreeZeroRegularity

open EquivariantCoefficients HodgeDegreeZeroCoefficientFormula
open CurveConventionCertificate Matrix
open scoped BigOperators

noncomputable section

/-- Polynomial torus-character coefficients with two separate formal Hodge variables. -/
abbrev RegularHodgePolynomial := MvPolynomial (Fin 2) Polynomial

/-- Rational formal Hodge polynomials after setting only torus characters to zero. -/
abbrev OrdinaryHodgePolynomial := MvPolynomial (Fin 2) ℚ

/-- The six monomials collect all nine ordered entries, retaining asymmetric sums. -/
theorem hodgePolynomial_expansion (c : Fin 3 → Fin 3 → Coefficient) :
    hodgePolynomial c =
      MvPolynomial.C (c 0 0) + MvPolynomial.C (c 0 1 + c 1 0) * MvPolynomial.X 0 +
      MvPolynomial.C (c 0 2 + c 2 0) * MvPolynomial.X 1 +
      MvPolynomial.C (c 1 1) * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C (c 1 2 + c 2 1) * MvPolynomial.X 0 * MvPolynomial.X 1 +
      MvPolynomial.C (c 2 2) * MvPolynomial.X 1 ^ 2 := by
  norm_num only [hodgePolynomial, hodgeGenerator, Fin.sum_univ_three, map_add,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  ring

namespace Plane

/-- Complete fixed-point sum of the actual decoded coefficient polynomials. -/
def completePolynomial : HodgePolynomial :=
  ∑ p : Fin 3, hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p)

/-- Explicit polynomial lift; the inner variables are the two torus characters. -/
def regularLift : RegularHodgePolynomial :=
  MvPolynomial.C (MvPolynomial.X 0 ^ 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.X 1 ^ 2) +
    3 * MvPolynomial.X 0 ^ 2 + (3) * MvPolynomial.X 1

/-- The ordinary formal polynomial, retaining both independent Hodge symbols. -/
def ordinaryPolynomial : OrdinaryHodgePolynomial :=
  3 * MvPolynomial.X 0 ^ 2 + (3) * MvPolynomial.X 1

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_constant :
    (∑ p : Fin 3,
      (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 0 0)) =
      x ^ 2 - x * y + y ^ 2 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.Plane.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.Plane.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.Plane.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda1 :
    (∑ p : Fin 3,
      (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 0 1 +
       HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 1 0)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.Plane.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.Plane.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.Plane.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda2 :
    (∑ p : Fin 3,
      (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 0 2 +
       HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 2 0)) =
      3 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.Plane.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.Plane.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.Plane.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda1Squared :
    (∑ p : Fin 3,
      (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 1 1)) =
      3 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.Plane.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.Plane.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.Plane.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_mixed :
    (∑ p : Fin 3,
      (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 1 2 +
       HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 2 1)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.Plane.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.Plane.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.Plane.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda2Squared :
    (∑ p : Fin 3,
      (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p 2 2)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.Plane.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.Plane.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.Plane.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- The full localized expression is the image of one polynomial lift. -/
theorem map_embed_regularLift :
    MvPolynomial.map embed regularLift = completePolynomial := by
  simp only [completePolynomial, hodgePolynomial_expansion, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← map_sum]
  simp only [← Finset.sum_add_distrib]
  rw [sum_constant, sum_lambda1, sum_lambda2, sum_lambda1Squared, sum_mixed,
    sum_lambda2Squared]
  norm_num only [regularLift, map_add, map_sub, map_neg, map_mul, map_pow,
    map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,
    embed_X_zero, embed_X_one, map_zero, zero_mul, zero_add, add_zero]
  ring

/-- Evaluate the polynomial lift at zero only after all fixed-point poles cancel. -/
theorem map_atZero_regularLift :
    MvPolynomial.map atZero regularLift = ordinaryPolynomial := by
  norm_num only [regularLift, ordinaryPolynomial, atZero, map_add, map_sub, map_neg,
    map_mul, map_pow, map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow, sub_zero, neg_zero]

end Plane

namespace OneBlowup

/-- Complete fixed-point sum of the actual decoded coefficient polynomials. -/
def completePolynomial : HodgePolynomial :=
  ∑ p : Fin 4, hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p)

/-- Explicit polynomial lift; the inner variables are the two torus characters. -/
def regularLift : RegularHodgePolynomial :=
  MvPolynomial.C (0) +
    4 * MvPolynomial.X 0 ^ 2 + (0) * MvPolynomial.X 1

/-- The ordinary formal polynomial, retaining both independent Hodge symbols. -/
def ordinaryPolynomial : OrdinaryHodgePolynomial :=
  4 * MvPolynomial.X 0 ^ 2 + (0) * MvPolynomial.X 1

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_constant :
    (∑ p : Fin 4,
      (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 0 0)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.OneBlowup.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.OneBlowup.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda1 :
    (∑ p : Fin 4,
      (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 0 1 +
       HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 1 0)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.OneBlowup.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.OneBlowup.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda2 :
    (∑ p : Fin 4,
      (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 0 2 +
       HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 2 0)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.OneBlowup.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.OneBlowup.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda1Squared :
    (∑ p : Fin 4,
      (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 1 1)) =
      4 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.OneBlowup.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.OneBlowup.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_mixed :
    (∑ p : Fin 4,
      (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 1 2 +
       HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 2 1)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.OneBlowup.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.OneBlowup.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda2Squared :
    (∑ p : Fin 4,
      (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p 2 2)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.OneBlowup.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.OneBlowup.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- The full localized expression is the image of one polynomial lift. -/
theorem map_embed_regularLift :
    MvPolynomial.map embed regularLift = completePolynomial := by
  simp only [completePolynomial, hodgePolynomial_expansion, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← map_sum]
  simp only [← Finset.sum_add_distrib]
  rw [sum_constant, sum_lambda1, sum_lambda2, sum_lambda1Squared, sum_mixed,
    sum_lambda2Squared]
  norm_num only [regularLift, map_add, map_sub, map_neg, map_mul, map_pow,
    map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,
    embed_X_zero, embed_X_one, map_zero, zero_mul, zero_add, add_zero]

/-- Evaluate the polynomial lift at zero only after all fixed-point poles cancel. -/
theorem map_atZero_regularLift :
    MvPolynomial.map atZero regularLift = ordinaryPolynomial := by
  norm_num only [regularLift, ordinaryPolynomial, atZero, map_add, map_sub, map_neg,
    map_mul, map_pow, map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow, sub_zero, neg_zero]

end OneBlowup

namespace TwoBlowups

/-- Complete fixed-point sum of the actual decoded coefficient polynomials. -/
def completePolynomial : HodgePolynomial :=
  ∑ p : Fin 5, hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p)

/-- Explicit polynomial lift; the inner variables are the two torus characters. -/
def regularLift : RegularHodgePolynomial :=
  MvPolynomial.C (-(MvPolynomial.X 0 ^ 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.X 1 ^ 2)) +
    5 * MvPolynomial.X 0 ^ 2 + (-3) * MvPolynomial.X 1

/-- The ordinary formal polynomial, retaining both independent Hodge symbols. -/
def ordinaryPolynomial : OrdinaryHodgePolynomial :=
  5 * MvPolynomial.X 0 ^ 2 + (-3) * MvPolynomial.X 1

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_constant :
    (∑ p : Fin 5,
      (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 0 0)) =
      -(x ^ 2 - x * y + y ^ 2) := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.TwoBlowups.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.TwoBlowups.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda1 :
    (∑ p : Fin 5,
      (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 0 1 +
       HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 1 0)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.TwoBlowups.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.TwoBlowups.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda2 :
    (∑ p : Fin 5,
      (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 0 2 +
       HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 2 0)) =
      -3 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.TwoBlowups.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.TwoBlowups.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda1Squared :
    (∑ p : Fin 5,
      (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 1 1)) =
      5 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.TwoBlowups.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.TwoBlowups.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_mixed :
    (∑ p : Fin 5,
      (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 1 2 +
       HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 2 1)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.TwoBlowups.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.TwoBlowups.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- Exact cancellation in the complete fixed-point coefficient sum. -/
theorem sum_lambda2Squared :
    (∑ p : Fin 5,
      (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p 2 2)) =
      0 := by
  norm_num only [HodgeDegreeZeroCoefficientFormula.TwoBlowups.coefficients_eq_orderedChern,
      orderedChernCoefficient,
      HodgeDegreeZeroCoefficientFormula.TwoBlowups.tangentWeight,
      HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent, character,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_two, map_zero,
      map_one, map_add, map_mul, map_pow, embed_C, embed_X_zero,
      embed_X_one, one_mul, mul_one, zero_mul, mul_zero, zero_add,
      add_zero, div_one, pow_zero, pow_one, neg_one_mul, neg_zero,
      sub_zero, zero_sub, sub_self, Matrix.cons_val, Matrix.of_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Fin.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_zero,
      Fin.val_natCast, Fin.val_one', ite_true, ite_false]
  ring_nf
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,
    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]
  ring

/-- The full localized expression is the image of one polynomial lift. -/
theorem map_embed_regularLift :
    MvPolynomial.map embed regularLift = completePolynomial := by
  simp only [completePolynomial, hodgePolynomial_expansion, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← map_sum]
  simp only [← Finset.sum_add_distrib]
  rw [sum_constant, sum_lambda1, sum_lambda2, sum_lambda1Squared, sum_mixed,
    sum_lambda2Squared]
  norm_num only [regularLift, map_add, map_sub, map_neg, map_mul, map_pow,
    map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,
    embed_X_zero, embed_X_one, map_zero, zero_mul, zero_add, add_zero]
  ring

/-- Evaluate the polynomial lift at zero only after all fixed-point poles cancel. -/
theorem map_atZero_regularLift :
    MvPolynomial.map atZero regularLift = ordinaryPolynomial := by
  norm_num only [regularLift, ordinaryPolynomial, atZero, map_add, map_sub, map_neg,
    map_mul, map_pow, map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,
    MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero, zero_mul, mul_zero, zero_add,
    add_zero, zero_pow, sub_zero, neg_zero]

end TwoBlowups

end

end AxiomaticGW.GKM.HodgeDegreeZeroRegularity
