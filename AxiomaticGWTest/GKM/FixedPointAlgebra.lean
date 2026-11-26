/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.FixedPointAlgebra
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-!
# Inverse Euler normalization regressions

Distinct Euler factors make a missing weight or an inverted inverse metric
observable. These are algebraic fixtures, not geometric GKM invariants.
-/

namespace AxiomaticGWTest.GKM.FixedPointAlgebra

open AxiomaticGW.GKM.FixedPointAlgebra

def euler : Fin 2 → ℚˣ :=
  ![Units.mk0 2 (by norm_num), Units.mk0 3 (by norm_num)]

example : counit euler ![5, 7] = (29 / 6 : ℚ) := by
  rw [counit_apply]
  norm_num only [euler, Fin.sum_univ_succ, Fintype.sum_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Units.val_inv_eq_inv_val, Units.val_mk0]

example : (algebra euler).pairing.form ![5, 7] ![11, 13] = (347 / 6 : ℚ) := by
  rw [AxiomaticGW.CommFrobeniusAlgebra.pairing_apply]
  change counit euler (![5, 7] * ![11, 13]) = (347 / 6 : ℚ)
  rw [counit_apply]
  norm_num only [euler, Pi.mul_apply, Fin.sum_univ_succ, Fintype.sum_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Units.val_inv_eq_inv_val, Units.val_mk0]

example : (algebra euler).pairing.form
    (Pi.single (0 : Fin 2) 1) (Pi.single (0 : Fin 2) 1) = (1 / 2 : ℚ) := by
  rw [algebra_pairing_single_right, Pi.single_eq_same]
  norm_num only [euler, Matrix.cons_val_zero, Units.val_inv_eq_inv_val,
    Units.val_mk0, mul_one]

example : inverseMetricMatrix euler (1 : Fin 2) 1 = 3 := by
  rw [inverseMetricMatrix, Matrix.diagonal_apply_eq]
  norm_num only [euler, Matrix.cons_val_one, Matrix.cons_val_zero, Units.val_mk0]

example (a : Fin 2 → ℚ) :
    a = ∑ p, ((euler p : ℚ) * (algebra euler).pairing.form a (Pi.single p 1)) •
      Pi.single p 1 := expansion_from_pairing euler a

end AxiomaticGWTest.GKM.FixedPointAlgebra
