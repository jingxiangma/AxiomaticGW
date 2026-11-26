/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.CalibrationSewingFrame

/-! # Exact nonlinear calibration sewing on the three research surfaces -/

@[expose] public section
namespace AxiomaticGW.GKM.CalibrationSewing
open EquivariantCoefficients Matrix EquivariantCalibrationReplay
open BlowupQuantumIdempotents (Index Direction)
open SmallQuantumGeneratorComparison (generator)
noncomputable section

open CalibrationSewingData

private abbrev TorusTerms := RationalTerms (Fin 2)

private def characters : Fin 2 → Coefficient := ![x,y]

private def dictionarySize : SurfaceTarget → ℕ
  | .plane => Plane.dictionarySize
  | .hirzebruchOne => OneBlowup.dictionarySize
  | .blowupTwo => TwoBlowups.dictionarySize

private def dictionaryTerms : (X : SurfaceTarget) → Fin (dictionarySize X) → TorusTerms
  | .plane => Plane.terms
  | .hirzebruchOne => OneBlowup.terms
  | .blowupTwo => TwoBlowups.terms

private def dictionaryValue : (X : SurfaceTarget) → Fin (dictionarySize X) → Coefficient
  | .plane => Plane.value x y
  | .hirzebruchOne => OneBlowup.value x y
  | .blowupTwo => TwoBlowups.value x y

private def metricIndex : (X : SurfaceTarget) →
    Matrix (Index X) (Index X) (Fin (dictionarySize X))
  | .plane => Plane.metricIndex
  | .hirzebruchOne => OneBlowup.metricIndex
  | .blowupTwo => TwoBlowups.metricIndex

private def endpointIndex : (X : SurfaceTarget) → Fin (rowCount X) →
    Matrix (Index X) (Index X) (Fin (dictionarySize X))
  | .plane => Plane.endpointIndex
  | .hirzebruchOne => OneBlowup.endpointIndex
  | .blowupTwo => TwoBlowups.endpointIndex

private def primitiveIndex : (X : SurfaceTarget) → Fin 3 → Direction X →
    Matrix (Index X) (Index X) (Fin (dictionarySize X))
  | .plane => Plane.primitiveIndex
  | .hirzebruchOne => OneBlowup.primitiveIndex
  | .blowupTwo => TwoBlowups.primitiveIndex

set_option maxHeartbeats 1500000 in
-- Evaluate each native polynomial once, independently of its positions in the source matrices.
private theorem eval_dict (X : SurfaceTarget) (q : Fin (dictionarySize X)) :
    RationalTerms.eval characters (dictionaryTerms X q) = dictionaryValue X q := by
  cases X
  · change RationalTerms.eval characters (Plane.terms q) = Plane.value x y q
    revert q
    change ∀ q : Fin 8, _
    intro q
    fin_cases q <;> dsimp +decide [Plane.terms, Plane.value] <;>
      norm_num [RationalTerms.eval, characters, Multiset.map_cons, Multiset.prod_cons,
        Multiset.sum_cons]
    ring
  · change RationalTerms.eval characters (OneBlowup.terms q) = OneBlowup.value x y q
    revert q
    change ∀ q : Fin 15, _
    intro q
    fin_cases q <;> dsimp +decide [OneBlowup.terms, OneBlowup.value] <;>
      norm_num [RationalTerms.eval, characters, Multiset.map_cons, Multiset.prod_cons,
        Multiset.sum_cons] <;> ring
  · change RationalTerms.eval characters (TwoBlowups.terms q) = TwoBlowups.value x y q
    revert q
    change ∀ q : Fin 27, _
    intro q
    fin_cases q <;> dsimp +decide [TwoBlowups.terms, TwoBlowups.value] <;>
      norm_num [RationalTerms.eval, characters, Multiset.map_cons, Multiset.prod_cons,
        Multiset.sum_cons] <;> ring

private theorem metric_value (X : SurfaceTarget) (i j : Index X) :
    dictionaryValue X (metricIndex X i j) = (tables X).inverseMetric i j := by
  rw [metric_eq]
  cases X <;> rfl

private theorem endpoint_value (X : SurfaceTarget) (r : Fin (rowCount X)) (i j : Index X) :
    dictionaryValue X (endpointIndex X r i j) = endpoint X r i j := by cases X <;> rfl

private theorem primitive_value (X : SurfaceTarget) (k : Fin 3) (d : Direction X) (i j : Index X) :
    dictionaryValue X (primitiveIndex X k d i j) = paired X k d i j := by
  cases X
  · fin_cases k <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
      first | rfl | (simp +decide [dictionaryValue, primitiveIndex, Plane.value,
        Plane.primitiveIndex, paired, EquivariantCalibrationData.Plane.paired,
        EquivariantCalibrationData.Plane.poly, Matrix.cons_val_two]; ring)
  · fin_cases k <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
      first | rfl | (simp +decide [dictionaryValue, primitiveIndex, OneBlowup.value,
        OneBlowup.primitiveIndex, paired, EquivariantCalibrationData.OneBlowup.paired,
        EquivariantCalibrationData.OneBlowup.poly, Matrix.cons_val_two]; ring)
  · fin_cases k <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
      first | rfl | (simp +decide [dictionaryValue, primitiveIndex, TwoBlowups.value,
        TwoBlowups.primitiveIndex, paired, EquivariantCalibrationData.TwoBlowups.paired,
        EquivariantCalibrationData.TwoBlowups.poly, Matrix.cons_val_two]; ring)

private def contraction {X : SurfaceTarget} (c : Direction X × Direction X) (k : Fin 3 × Fin 3)
    (i j : Index X) : TorusTerms :=
  ∑ h, RationalTerms.mul (dictionaryTerms X (primitiveIndex X k.1 c.1 h i))
    (∑ t, RationalTerms.mul (dictionaryTerms X (metricIndex X h t))
      (dictionaryTerms X (primitiveIndex X k.2 c.2 t j)))

private theorem eval_contraction {X : SurfaceTarget} (c : Direction X × Direction X)
    (k : Fin 3 × Fin 3) (i j : Index X) :
    RationalTerms.eval characters (contraction c k i j) =
      ((paired X k.1 c.1).transpose * ((tables X).inverseMetric * paired X k.2 c.2)) i j := by
  simp only [contraction, RationalTerms.eval_sum, RationalTerms.eval_mul, eval_dict,
    metric_value, primitive_value, Matrix.mul_apply, Matrix.transpose_apply]

private def interiorTerms {X : SurfaceTarget} (s : Row X) (i j : Index X) : TorusTerms :=
  (s.cuts.map fun c ↦ (s.power.cuts.map fun k ↦
    RationalTerms.scale ((-1 : ℚ)^(k.1.val+1)) (contraction c k i j)).sum).sum

private theorem eval_interior {X : SurfaceTarget} (s : Row X) (i j : Index X) :
    RationalTerms.eval characters (interiorTerms s i j) =
      interior s (tables X).inverseMetric i j := by
  cases hp : s.power <;> by_cases hd : s.left = s.right <;>
    simp [interiorTerms, interior, Row.cuts, Power.cuts, hp, hd, RationalTerms.eval_add,
      RationalTerms.eval_scale, eval_contraction, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, map_pow]

private def rowTerms (X : SurfaceTarget) (r : Fin (rowCount X)) (i j : Index X) : TorusTerms :=
  dictionaryTerms X (endpointIndex X r i j) +
    RationalTerms.scale ((-1 : ℚ)^(row X r).power.val)
      (dictionaryTerms X (endpointIndex X r j i)) +
    interiorTerms (row X r) i j

private theorem eval_row (X : SurfaceTarget) (r : Fin (rowCount X)) (i j : Index X) :
    RationalTerms.eval characters (rowTerms X r i j) = coefficient X r i j := by
  simp only [rowTerms, coefficient, RationalTerms.eval_add, RationalTerms.eval_scale, eval_dict,
    endpoint_value, eval_interior, Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
    map_pow, map_neg, map_one, smul_eq_mul]

set_option maxHeartbeats 5000000 in
-- Collect the actual bivariate products, including both torus characters, in the kernel.
private theorem checked (X : SurfaceTarget) :
    ∀ (r : Fin (rowCount X)) (i j : Index X),
      RationalTerms.checkEquivalent (rowTerms X r i j) 0 = true := by
  cases X <;> decide +kernel

/-- The held nonprimitive sewing coefficient vanishes in the full bivariate fraction field. -/
theorem coefficient_zero (X : SurfaceTarget) (r : Fin (rowCount X)) : coefficient X r = 0 := by
  funext i j
  rw [← eval_row]
  exact RationalTerms.eval_eq_of_equivalent characters _ 0
    ((RationalTerms.checkEquivalent_eq_true _ _).mp (checked X r i j))

end
end AxiomaticGW.GKM.CalibrationSewing
