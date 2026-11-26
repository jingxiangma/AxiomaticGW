/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.StateSpaceTransport
import AxiomaticGW.CohFT.Constant
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-!
# A mixed basis with distinct Euler weights

The second basis vector squares to the first after restriction. Its metric
has a nonzero off-diagonal entry. These regressions detect using pointwise
multiplication on coefficient vectors or dropping the inverse Euler factors.
The supplied full CohFT is the existing nontrivial constant-target model,
not a geometric surface theory.
-/

namespace AxiomaticGWTest.GKM.StateSpaceTransport

open AxiomaticGW AxiomaticGW.GKM.StateSpaceTransport
open Matrix

def euler : Fin 2 → ℚˣ :=
  ![Units.mk0 2 (by norm_num), Units.mk0 3 (by norm_num)]

def restrictions : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, -1]

def inverse : Matrix (Fin 2) (Fin 2) ℚ := !![1/2, 1/2; 1/2, -1/2]

theorem restrictions_inverse : restrictions * inverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num only [restrictions, inverse, Matrix.mul_apply, Fin.sum_univ_succ,
      Fintype.sum_empty, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Matrix.one_apply, Fin.mk.injEq, ite_true, ite_false]

theorem inverse_restrictions : inverse * restrictions = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num only [restrictions, inverse, Matrix.mul_apply, Fin.sum_univ_succ,
      Fintype.sum_empty, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Matrix.one_apply, Fin.mk.injEq, ite_true, ite_false]

def equivalence : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  basisEquiv restrictions inverse restrictions_inverse inverse_restrictions

example : unit equivalence = ![1, 0] := by
  change inverse *ᵥ (1 : Fin 2 → ℚ) = _
  ext i
  fin_cases i <;>
    norm_num only [inverse, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fintype.sum_empty, Pi.one_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]

example : product equivalence ![0, 1] ![0, 1] = ![1, 0] := by
  apply equivalence.injective
  rw [restriction_product]
  change (restrictions *ᵥ ![0, 1]) * (restrictions *ᵥ ![0, 1]) = restrictions *ᵥ ![1, 0]
  ext i
  fin_cases i <;>
    norm_num only [restrictions, Matrix.mulVec, dotProduct, Pi.mul_apply,
      Fin.sum_univ_succ, Fintype.sum_empty, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]

theorem mixed_metric :
    ((GKM.FixedPointAlgebra.algebra euler).pairing.comap equivalence).form
      (Pi.single (0 : Fin 2) 1) (Pi.single (1 : Fin 2) 1) = (1/6 : ℚ) := by
  have h : metricMatrix euler restrictions (0 : Fin 2) 1 = (1/6 : ℚ) := by
    have hzero : (0 : Fin 2) ≠ (0 : Fin 1).succ := (Fin.succ_ne_zero _).symm
    norm_num only [metricMatrix, GKM.FixedPointAlgebra.metricMatrix, restrictions, euler,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal, Fin.sum_univ_succ,
      Fintype.sum_empty, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Units.val_inv_eq_inv_val, Units.val_mk0, Fin.mk.injEq,
      Fin.succ_ne_zero, hzero, ite_true, ite_false]
  exact (pairing_basis euler restrictions inverse restrictions_inverse inverse_restrictions
    (0 : Fin 2) (1 : Fin 2)).trans h

noncomputable def original : CohFT ℚ (Fin 2 → ℚ) (constantStableCurveCohomology ℚ) :=
  (GKM.FixedPointAlgebra.algebra euler).toTopologicalCohFT.toConstantCohFT

noncomputable def transported := original.comap equivalence

example : transported.unit = unit equivalence := rfl

example : transported.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
    (fun | none => transported.unit
         | some i => Pi.single i 1) = (1/6 : ℚ) := by
  have h := transported.normalization (fun i : Fin 2 ↦ Pi.single i 1)
  change transported.omega 0 (Option (Fin 2)) StableArity.zero_option_fin_two
    (fun | none => transported.unit | some i => Pi.single i 1) =
      transported.pairing.form (Pi.single 0 1) (Pi.single 1 1) at h
  exact h.trans mixed_metric

example (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (a : S → Fin 2 → ℚ) :
    (transported.comap equivalence.symm).omega g S h a = original.omega g S h a :=
  original.comap_omega_roundTrip equivalence g S h a

end AxiomaticGWTest.GKM.StateSpaceTransport
