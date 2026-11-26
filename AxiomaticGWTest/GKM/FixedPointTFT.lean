module

public import AxiomaticGW.GKM.FixedPointTFT
public import AxiomaticGW.CohFT.Topological
public import Mathlib.Tactic.NormNum

/-!
# Distinct Euler factors detect genus powers and inverse-metric normalization

These are algebraic tests of the existing Frobenius TFT. The stable one-point
consumer uses its actual bundled topological CohFT; no geometric GW input is asserted.
-/

@[expose] public section

namespace AxiomaticGWTest.GKM.FixedPointTFT

open AxiomaticGW GKM.FixedPointAlgebra GKM.FixedPointTFT

/-- Distinct invertible factors make an incorrect genus weight observable. -/
def euler : Fin 2 → ℚˣ :=
  ![Units.mk0 2 (by norm_num), Units.mk0 3 (by norm_num)]

/-- The canonical handle retains the two distinct Euler factors. -/
theorem handle_coordinates : (algebra euler).handleElement = ![2, 3] := by
  rw [handleElement_eq]
  funext p
  fin_cases p <;> rfl

/-- Genus-zero empty arity retains inverse Euler weights. -/
theorem genus_zero_empty : (algebra euler).correlator 0 Empty (fun s ↦ nomatch s) = 5 / 6 := by
  rw [correlator_eq]
  norm_num only [euler, Fin.sum_univ_succ, Fintype.sum_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Units.val_inv_eq_inv_val, Units.val_mk0, pow_zero, mul_one,
    Fintype.prod_empty]

/-- The genus-one empty correlator counts the two idempotent summands. -/
theorem genus_one_empty : (algebra euler).correlator 1 Empty (fun s ↦ nomatch s) = 2 := by
  rw [correlator_eq]
  norm_num only [euler, Fin.sum_univ_succ, Fintype.sum_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Units.val_inv_eq_inv_val, Units.val_mk0, pow_one, mul_one,
    Fintype.prod_empty]

/-- The empty genus-two value is the sum, not the inverse sum, of the Euler factors. -/
theorem genus_two_empty : (algebra euler).correlator 2 Empty (fun s ↦ nomatch s) = 5 := by
  rw [correlator_eq]
  norm_num only [euler, Fin.sum_univ_succ, Fintype.sum_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Units.val_inv_eq_inv_val, Units.val_mk0, Fintype.prod_empty]

/-- A nonunit insertion tests multiplication by the genus-two Euler weight. -/
theorem genus_two_one_point :
    (algebra euler).correlator 2 (Fin 1) (fun _ ↦ ![5, 7]) = 31 := by
  rw [correlator_eq]
  norm_num only [euler, Fin.sum_univ_succ, Fintype.sum_empty,
    Fin.prod_univ_succ, Fintype.prod_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Units.val_inv_eq_inv_val, Units.val_mk0]

/-- The actual stable topological CohFT has the derived genus-two unit value. -/
theorem topological_genus_two_unit :
    (algebra euler).toTopologicalCohFT.omega 2 (Fin 1)
      (by norm_num only [StableArity, Fintype.card_fin])
      (fun _ ↦ (algebra euler).toTopologicalCohFT.unit) = 5 := by
  change (algebra euler).correlator 2 (Fin 1) (fun _ ↦ 1) = 5
  rw [correlator_two_unit]
  norm_num only [euler, Fin.sum_univ_succ, Fintype.sum_empty,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Units.val_mk0]

/-- The same bundled TFT retains the original three-point metric normalization. -/
theorem topological_unit_normalization (a : Fin 2 → Fin 2 → ℚ) :
    (algebra euler).toTopologicalCohFT.omega 0 (Option (Fin 2))
      StableArity.zero_option_fin_two
      (fun | none => (algebra euler).toTopologicalCohFT.unit | some i => a i) =
      (algebra euler).pairing.form (a 0) (a 1) :=
  (algebra euler).toTopologicalCohFT.normalization a

end AxiomaticGWTest.GKM.FixedPointTFT
