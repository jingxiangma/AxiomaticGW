/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroFullCoefficientReplay
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# All actual ordered coefficients satisfy the formal genus-two Chern formula

The held producer orders lambda indices with its two ordered tangent weights.
At genus two its coefficient is (-1)^(a+b) w₀^(1-a) w₁^(1-b).
The equivalent common-denominator form below uses only natural exponents.
Every equality is proved for the actual upstream decoded fraction, not a replacement.
The bivariate variables are formal lambda₁ and lambda₂, with lambda₀ = 1.
No geometric Hodge/Chern/GRR, GW, realization or CohFT identification is made.
-/

@[expose] public section

namespace AxiomaticGW.GKM.HodgeDegreeZeroCoefficientFormula

open EquivariantCoefficients CurveConventionCertificate Matrix
open scoped BigOperators

noncomputable section

/-- Ordered rank-two Chern coefficient divided by the two tangent weights. -/
def orderedChernCoefficient (w₀ w₁ : Coefficient) (a b : Fin 3) : Coefficient :=
  (-1 : Coefficient) ^ (a.val + b.val) * w₀ ^ (2 - a.val) * w₁ ^ (2 - b.val) /
    (w₀ * w₁)

/-- Two formal Hodge symbols over the existing exact equivariant field. -/
abbrev HodgePolynomial := MvPolynomial (Fin 2) Coefficient

/-- Formal lambda₀, lambda₁ and lambda₂, with lambda₀ equal to one. -/
def hodgeGenerator : Fin 3 → HodgePolynomial := ![1, MvPolynomial.X 0, MvPolynomial.X 1]

/-- Keep all nine ordered coefficients before collecting formal monomials. -/
def hodgePolynomial (coeff : Fin 3 → Fin 3 → Coefficient) : HodgePolynomial :=
  ∑ a, ∑ b, MvPolynomial.C (coeff a b) * hodgeGenerator a * hodgeGenerator b

/-- The rank-two formal Chern polynomial at one tangent weight. -/
def chernPolynomial (w : Coefficient) : HodgePolynomial :=
  MvPolynomial.C (w ^ 2) - MvPolynomial.C w * MvPolynomial.X 0 + MvPolynomial.X 1

/-- Algebraic expansion with shared formal Hodge symbols; no geometric class input. -/
theorem hodgePolynomial_orderedChernCoefficient (w₀ w₁ : Coefficient) :
    hodgePolynomial (orderedChernCoefficient w₀ w₁) =
      MvPolynomial.C ((w₀ * w₁)⁻¹) * chernPolynomial w₀ * chernPolynomial w₁ := by
  norm_num only [hodgePolynomial, orderedChernCoefficient, hodgeGenerator,
      chernPolynomial, Fin.sum_univ_succ, Fin.sum_univ_zero,
      div_eq_mul_inv, map_mul, map_pow, map_neg, map_one,
      Matrix.cons_val, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  ring

namespace Plane

/-- Reuse the actual ordered tangent characters; no tangent table is substituted. -/
def tangentWeight (p : Fin 3) (j : Fin 2) : Coefficient :=
  character (HodgeDegreeZeroCoefficientReplay.Plane.tangent p j)

/-- The actual product is nonzero because its already checked Euler weight is a unit. -/
theorem tangentProduct_ne_zero (p : Fin 3) :
    tangentWeight p 0 * tangentWeight p 1 ≠ 0 := by
  change character (HodgeDegreeZeroCoefficientReplay.Plane.tangent p 0) *
    character (HodgeDegreeZeroCoefficientReplay.Plane.tangent p 1) ≠ 0
  rw [← HodgeDegreeZeroCoefficientReplay.Plane.coefficient00_eq_tangentProduct,
    HodgeDegreeZeroCoefficientReplay.Plane.coefficient00_eq_eulerUnits]
  exact Units.ne_zero (SurfaceReplay.Plane.accepted.eulerUnits p)

/-- Every actual serialized coefficient agrees with the ordered source formula. -/
theorem coefficients_eq_orderedChern (p : Fin 3) (a b : Fin 3) :
    HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p a b =
      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) a b := by
  unfold HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients orderedChernCoefficient
  apply (div_eq_div_iff (HodgeDegreeZeroFullCoefficientReplay.Plane.denominator_ne_zero p a b)
    (tangentProduct_ne_zero p)).mpr
  fin_cases p <;> fin_cases a <;> fin_cases b
  all_goals norm_num only [HodgeDegreeZeroFullCoefficientReplay.Plane.numerators,
      HodgeDegreeZeroFullCoefficientReplay.Plane.denominators,
      tangentWeight, HodgeDegreeZeroCoefficientReplay.Plane.tangent,
      character, map_zero, map_one, map_add, map_mul, map_pow, embed_C,
      embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, div_one, pow_zero, pow_one, neg_one_mul,
      neg_zero, sub_zero, zero_sub, sub_self, Matrix.cons_val,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals ring

/-- The complete actual bivariate polynomial factors into both formal Chern factors. -/
theorem hodgePolynomial_eq (p : Fin 3) :
    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p) =
      MvPolynomial.C ((tangentWeight p 0 * tangentWeight p 1)⁻¹) *
        chernPolynomial (tangentWeight p 0) * chernPolynomial (tangentWeight p 1) := by
  have h : HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p =
      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) := by
    funext a b
    exact coefficients_eq_orderedChern p a b
  rw [h]
  exact hodgePolynomial_orderedChernCoefficient _ _

end Plane

namespace OneBlowup

/-- Reuse the actual ordered tangent characters; no tangent table is substituted. -/
def tangentWeight (p : Fin 4) (j : Fin 2) : Coefficient :=
  character (HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent p j)

/-- The actual product is nonzero because its already checked Euler weight is a unit. -/
theorem tangentProduct_ne_zero (p : Fin 4) :
    tangentWeight p 0 * tangentWeight p 1 ≠ 0 := by
  change character (HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent p 0) *
    character (HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent p 1) ≠ 0
  rw [← HodgeDegreeZeroCoefficientReplay.OneBlowup.coefficient00_eq_tangentProduct,
    HodgeDegreeZeroCoefficientReplay.OneBlowup.coefficient00_eq_eulerUnits]
  exact Units.ne_zero (SurfaceReplay.OneBlowup.accepted.eulerUnits p)

/-- Every actual serialized coefficient agrees with the ordered source formula. -/
theorem coefficients_eq_orderedChern (p : Fin 4) (a b : Fin 3) :
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p a b =
      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) a b := by
  unfold HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients orderedChernCoefficient
  apply (div_eq_div_iff (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.denominator_ne_zero p a b)
    (tangentProduct_ne_zero p)).mpr
  fin_cases p <;> fin_cases a <;> fin_cases b
  all_goals norm_num only [HodgeDegreeZeroFullCoefficientReplay.OneBlowup.numerators,
      HodgeDegreeZeroFullCoefficientReplay.OneBlowup.denominators,
      tangentWeight, HodgeDegreeZeroCoefficientReplay.OneBlowup.tangent,
      character, map_zero, map_one, map_add, map_mul, map_pow, embed_C,
      embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, div_one, pow_zero, pow_one, neg_one_mul,
      neg_zero, sub_zero, zero_sub, sub_self, Matrix.cons_val,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals ring

/-- The complete actual bivariate polynomial factors into both formal Chern factors. -/
theorem hodgePolynomial_eq (p : Fin 4) :
    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p) =
      MvPolynomial.C ((tangentWeight p 0 * tangentWeight p 1)⁻¹) *
        chernPolynomial (tangentWeight p 0) * chernPolynomial (tangentWeight p 1) := by
  have h : HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p =
      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) := by
    funext a b
    exact coefficients_eq_orderedChern p a b
  rw [h]
  exact hodgePolynomial_orderedChernCoefficient _ _

end OneBlowup

namespace TwoBlowups

/-- Reuse the actual ordered tangent characters; no tangent table is substituted. -/
def tangentWeight (p : Fin 5) (j : Fin 2) : Coefficient :=
  character (HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent p j)

/-- The actual product is nonzero because its already checked Euler weight is a unit. -/
theorem tangentProduct_ne_zero (p : Fin 5) :
    tangentWeight p 0 * tangentWeight p 1 ≠ 0 := by
  change character (HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent p 0) *
    character (HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent p 1) ≠ 0
  rw [← HodgeDegreeZeroCoefficientReplay.TwoBlowups.coefficient00_eq_tangentProduct,
    HodgeDegreeZeroCoefficientReplay.TwoBlowups.coefficient00_eq_eulerUnits]
  exact Units.ne_zero (SurfaceReplay.TwoBlowups.accepted.eulerUnits p)

/-- Every actual serialized coefficient agrees with the ordered source formula. -/
theorem coefficients_eq_orderedChern (p : Fin 5) (a b : Fin 3) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p a b =
      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) a b := by
  unfold HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients orderedChernCoefficient
  apply (div_eq_div_iff (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.denominator_ne_zero p a b)
    (tangentProduct_ne_zero p)).mpr
  fin_cases p <;> fin_cases a <;> fin_cases b
  all_goals norm_num only [HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.numerators,
      HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.denominators,
      tangentWeight, HodgeDegreeZeroCoefficientReplay.TwoBlowups.tangent,
      character, map_zero, map_one, map_add, map_mul, map_pow, embed_C,
      embed_X_zero, embed_X_one, one_mul, mul_one, zero_mul, mul_zero,
      zero_add, add_zero, div_one, pow_zero, pow_one, neg_one_mul,
      neg_zero, sub_zero, zero_sub, sub_self, Matrix.cons_val,
      Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Fin.mk.injEq,
      Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.val_natCast,
      Fin.val_one', ite_true, ite_false]
  all_goals ring

/-- The complete actual bivariate polynomial factors into both formal Chern factors. -/
theorem hodgePolynomial_eq (p : Fin 5) :
    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p) =
      MvPolynomial.C ((tangentWeight p 0 * tangentWeight p 1)⁻¹) *
        chernPolynomial (tangentWeight p 0) * chernPolynomial (tangentWeight p 1) := by
  have h : HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p =
      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) := by
    funext a b
    exact coefficients_eq_orderedChern p a b
  rw [h]
  exact hodgePolynomial_orderedChernCoefficient _ _

end TwoBlowups

end

end AxiomaticGW.GKM.HodgeDegreeZeroCoefficientFormula
