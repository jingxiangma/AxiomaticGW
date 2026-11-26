module

import AxiomaticGW.GKM.HomogeneousSpecialization
import Mathlib.Tactic.FinCases

set_option linter.privateModule false
namespace AxiomaticGWTest.GKM.HomogeneousSpecialization
open AxiomaticGW.GKM.EquivariantCoefficients MvPolynomial

-- The quotient y/x has degree zero. A regular value would force the polynomial identity y = q x.
example (q : ℚ) : ¬ Specializes (y / x) q := by
  intro h
  have he := eq_constant_of_homogeneous (isHomogeneous_X ℚ (1 : Fin 2))
    (isHomogeneous_X ℚ (0 : Fin 2)) x_ne_zero h
  have hp : (X 1 : Polynomial) = C q * X 0 := by
    apply IsFractionRing.injective Polynomial Coefficient
    change embed (X 1) = embed (C q * X 0)
    rw [map_mul, embed_C, embed_X_zero]
    exact (div_eq_iff x_ne_zero).mp he
  have err := congrArg (eval₂Hom (RingHom.id ℚ) ![0, 1]) hp
  apply (one_ne_zero : (1 : ℚ) ≠ 0)
  simpa only [eval₂Hom_X', map_mul, eval₂Hom_C, RingHom.id_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, mul_zero] using err

-- The numerator can be non-homogeneous in a regular presentation of the constant one.
example : embed (X (0 : Fin 2)) / embed (X 0) = ((1 : ℚ) : Coefficient) := by
  apply eq_constant_of_homogeneous (isHomogeneous_X ℚ 0) (isHomogeneous_X ℚ 0) x_ne_zero
  have h : atZero (1 + X 1) = 1 := by
    rw [atZero, map_add, map_one, eval₂Hom_X', Pi.zero_apply, add_zero]
  have hn : atZero (1 + X 1) ≠ 0 := h ▸ one_ne_zero
  exact ⟨1 + X 1, 1 + X 1, hn, (div_self (embed_ne_zero_of_atZero _ hn)).trans
    (div_self x_ne_zero).symm, div_self hn⟩

end AxiomaticGWTest.GKM.HomogeneousSpecialization
