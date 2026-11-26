/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalCoverFactors

/-! # Regular and singular controls for exceptional character substitution -/

public section
namespace AxiomaticGWTest.GKM.ExceptionalCharacterField
open AxiomaticGW.GKM.EquivariantCoefficients AxiomaticGW.GKM.ExceptionalCharacterField
open AxiomaticGW.GKM.ExceptionalCoverFactors AxiomaticGW.GKM.CurveReplay
open MvPolynomial (C X)
noncomputable section

/-- A nonconstant regular fraction transports both symbolic terms and retains the value 2. -/
theorem regular_fraction : field ((2 + x) / (1 + y)) = (2 + (y - x)) / (1 - x) ∧
    Specializes (field ((2 + x) / (1 + y))) 2 := by
  constructor
  · rw [map_div₀, map_add, map_add, map_ofNat, map_one, field_generators.1, field_generators.2,
      sub_eq_add_neg 1]
  · apply (specializes_iff _ _).mpr
    refine ⟨C 2 + X 0, C 1 + X 1, ?_, ?_, ?_⟩
    · simp only [map_add, atZero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
        RingHom.id_apply, Pi.zero_apply, add_zero, ne_eq, one_ne_zero, not_false_eq_true]
    · rw [map_add, map_add, embed_C, embed_C, embed_X_zero, embed_X_one]
      norm_num
    · simp only [map_add, atZero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
        RingHom.id_apply, Pi.zero_apply, add_zero, div_one]

/-- The transported pole at x stays singular at every scalar ordinary value. -/
theorem pole (q : ℚ) : ¬ Specializes ((y - x)⁻¹) q := by
  have h : ¬ Specializes (x⁻¹) q := not_specializes_inverse (X 0) x_ne_zero
    (MvPolynomial.eval₂Hom_X' ..) q
  rw [← field_generators.1, ← map_inv₀, specializes_iff]
  exact h

/-- The unique normal obstruction of a double cover gives distinct, nonconstant fields on
the two exceptional axes. The separate deck-group order is two in each case. -/
theorem double_cover :
    atEdge OneBlowup.tables 2 2 = 2 * (x+y) / (x-y)^4 ∧
    atEdge TwoBlowups.tables 4 2 = 2 * (y-2*x) / y^4 := by
  have h (w n : Coefficient) (hw : w ≠ 0) : factor 2 w n = 2*(2*n+w)/w^4 := by
    change (-1 : Coefficient)^2 / (2 : Coefficient)^2 / (w / 2)^4 *
      (∏ j : Fin 1, (n + (j.val + 1 : Coefficient) * (w / 2))) = _
    rw [Fin.prod_univ_one]
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul]
    field_simp
  constructor
  · change factor 2 ((1 : ℤ)*x + (-1 : ℤ)*y) ((0 : ℤ)*x + (1 : ℤ)*y) = _
    push_cast
    simp only [one_mul, neg_one_mul, zero_mul, zero_add, ← sub_eq_add_neg]
    rw [h _ _ x_sub_y_ne_zero]
    ring
  · change factor 2 ((0 : ℤ)*x + (1 : ℤ)*y) ((-1 : ℤ)*x + (0 : ℤ)*y) = _
    push_cast
    simp only [one_mul, neg_one_mul, zero_mul, zero_add, add_zero]
    rw [h _ _ y_ne_zero]
    ring

end
end AxiomaticGWTest.GKM.ExceptionalCharacterField
