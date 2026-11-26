/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SemisimpleCalibration
public import AxiomaticGW.GKM.Fixtures.CalibrationSewingData

/-! # Nonprimitive coefficients of the two-point sewing equation

In S(-z)ᵀ η S(z), a positive inverse-loop power at a zero curve class vanishes.
For a sum of two generators the remaining interior contributions have two
positive primitive classes. Their order matters, and a double has only one
ordered curve split. The contraction uses the inverse toric metric.
-/

@[expose] public section
namespace AxiomaticGW.GKM.CalibrationSewing
open EquivariantCoefficients Matrix EquivariantCalibrationReplay
open BlowupQuantumIdempotents (Index Direction)
open SmallQuantumGeneratorComparison (generator)
noncomputable section

/-- The inverse-loop powers supported by the held composite-degree requests. -/
inductive Power | two | three | four deriving DecidableEq

/-- Inverse-loop exponent. -/
def Power.val : Power → ℕ | .two => 2 | .three => 3 | .four => 4

/-- Interior loop cuts as the two retained psi powers. Add one to each for inverse-loop power. -/
def Power.cuts : Power → List (Fin 3 × Fin 3)
  | .two => [(0,0)]
  | .three => [(0,1),(1,0)]
  | .four => [(0,2),(1,1),(2,0)]

/-- The two effective directions and the independently recorded total class. -/
structure Row (X : SurfaceTarget) where
  /-- Full effective class of the composite endpoint. -/
  beta : X.Curve
  /-- First primitive direction of the composite. -/
  left : Direction X
  /-- Second primitive direction, possibly equal to the first. -/
  right : Direction X
  /-- Requested coefficient of the inverse loop variable. -/
  power : Power

/-- Distinct ordered positive curve cuts. -/
def Row.cuts {X : SurfaceTarget} (s : Row X) : List (Direction X × Direction X) :=
  if s.left = s.right then [(s.left,s.right)] else [(s.left,s.right),(s.right,s.left)]

/-- All candidate rows are bound to their original effective coordinates. -/
abbrev rowCount : SurfaceTarget → ℕ | .plane => 1 | .hirzebruchOne => 4 | .blowupTwo => 8

/-- Effective curve and truncation determined by the benchmark request. -/
def row : (X : SurfaceTarget) → Fin (rowCount X) → Row X
  | .plane => ![⟨![2], 0, 0, .four⟩]
  | .hirzebruchOne => ![⟨![1,1], 0, 1, .two⟩, ⟨![1,1], 0, 1, .three⟩,
      ⟨![2,0], 0, 0, .two⟩, ⟨![2,0], 0, 0, .three⟩]
  | .blowupTwo => ![⟨![0,1,1], 1, 2, .two⟩, ⟨![0,1,1], 1, 2, .three⟩,
      ⟨![1,0,1], 0, 2, .two⟩, ⟨![1,0,1], 0, 2, .three⟩,
      ⟨![2,0,0], 0, 0, .two⟩, ⟨![2,0,0], 0, 0, .three⟩,
      ⟨![0,2,0], 1, 1, .two⟩, ⟨![0,2,0], 1, 1, .three⟩]

/-- Full effective coordinates and inverse-loop power read from the archived source row. -/
def sourceRequest : (X : SurfaceTarget) → Fin (rowCount X) → X.Curve × ℕ
  | .plane => CalibrationSewingData.Plane.request
  | .hirzebruchOne => CalibrationSewingData.OneBlowup.request
  | .blowupTwo => CalibrationSewingData.TwoBlowups.request

/-- The independently specified benchmark has the precise native request at every index. -/
theorem request_binding (X : SurfaceTarget) (r : Fin (rowCount X)) :
    ((row X r).beta, (row X r).power.val) = sourceRequest X r := by
  revert r
  cases X <;> decide +kernel

/-- Incoming paired coefficient at the full curve class. -/
def endpoint : (X : SurfaceTarget) → Fin (rowCount X) → Matrix (Index X) (Index X) Coefficient
  | .plane => CalibrationSewingData.Plane.paired x y
  | .hirzebruchOne => CalibrationSewingData.OneBlowup.paired x y
  | .blowupTwo => CalibrationSewingData.TwoBlowups.paired x y

/-- Compact presentation of the archived inverse metric. -/
def metricInverse : (X : SurfaceTarget) → Matrix (Index X) (Index X) Coefficient
  | .plane => CalibrationSewingData.Plane.inverseMetric x y
  | .hirzebruchOne => CalibrationSewingData.OneBlowup.inverseMetric x y
  | .blowupTwo => CalibrationSewingData.TwoBlowups.inverseMetric x y

/-- All nonzero ordered effective splittings occur exactly once. -/
theorem curve_cuts (X : SurfaceTarget) (r : Fin (rowCount X)) :
    let s := row X r
    let ks := s.cuts.map (fun c ↦ (generator X c.1, generator X c.2))
    ks.Nodup ∧ ks.toFinset = (X.splittings s.beta).filter (fun c ↦ c.1 ≠ 0 ∧ c.2 ≠ 0) := by
  revert r
  cases X <;> decide +kernel

/-- The positive powers give exactly the interior of the true antidiagonal. -/
theorem power_cuts (p : Power) :
    let ks := p.cuts.map (fun c ↦ (c.1.val+1,c.2.val+1))
    ks.Nodup ∧ ks.toFinset =
      (Finset.HasAntidiagonal.antidiagonal p.val).filter (fun c ↦ c.1 ≠ 0 ∧ c.2 ≠ 0) := by
  cases p <;> decide +kernel

/-- Two positive tails contracted along the common node, with (-z) on the first tail. -/
def interior {X : SurfaceTarget} (s : Row X) (G : Matrix (Index X) (Index X) Coefficient) :
    Matrix (Index X) (Index X) Coefficient :=
  (s.cuts.map fun c ↦ (s.power.cuts.map fun k ↦
    ((-1 : Coefficient)^(k.1.val+1)) •
      ((paired X k.1 c.1).transpose * (G * paired X k.2 c.2))).sum).sum

set_option maxHeartbeats 2000000 in
-- Reduce the source dictionary at each entry of the inverse metric.
private theorem metricPlane :
    (tables .plane).inverseMetric = metricInverse .plane := by
  funext i j
  change _ = CalibrationSewingData.Plane.inverseMetric x y i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [tables, SurfaceReplay.Plane.tables,
      SurfaceReplay.Plane.values, SurfaceReplay.Plane.numerators,
      SurfaceReplay.Plane.denominators,
      CalibrationSewingData.Plane.inverseMetric, CalibrationSewingData.Plane.metricIndex,
      CalibrationSewingData.Plane.value, Matrix.cons_val, Matrix.of_apply]
  all_goals norm_num [Matrix.cons_val, Matrix.of_apply, tables, SurfaceReplay.Plane.tables,
      SurfaceReplay.Plane.values, SurfaceReplay.Plane.numerators,
      SurfaceReplay.Plane.denominators,
      CalibrationSewingData.Plane.inverseMetric, CalibrationSewingData.Plane.metricIndex,
      CalibrationSewingData.Plane.value, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, Matrix.cons_val_two, Matrix.cons_val_three]

set_option maxHeartbeats 2000000 in
-- Reduce the source dictionary at each entry of the inverse metric.
private theorem metricOneBlowup :
    (tables .hirzebruchOne).inverseMetric = metricInverse .hirzebruchOne := by
  funext i j
  change _ = CalibrationSewingData.OneBlowup.inverseMetric x y i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [tables, SurfaceReplay.OneBlowup.tables,
      SurfaceReplay.OneBlowup.values, SurfaceReplay.OneBlowup.numerators,
      SurfaceReplay.OneBlowup.denominators,
      CalibrationSewingData.OneBlowup.inverseMetric, CalibrationSewingData.OneBlowup.metricIndex,
      CalibrationSewingData.OneBlowup.value, Matrix.cons_val, Matrix.of_apply]
  all_goals norm_num [Matrix.cons_val, Matrix.of_apply, tables, SurfaceReplay.OneBlowup.tables,
      SurfaceReplay.OneBlowup.values, SurfaceReplay.OneBlowup.numerators,
      SurfaceReplay.OneBlowup.denominators,
      CalibrationSewingData.OneBlowup.inverseMetric, CalibrationSewingData.OneBlowup.metricIndex,
      CalibrationSewingData.OneBlowup.value, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, Matrix.cons_val_two, Matrix.cons_val_three]

set_option maxHeartbeats 2000000 in
-- Reduce the source dictionary at each entry of the inverse metric.
private theorem metricTwoBlowups :
    (tables .blowupTwo).inverseMetric = metricInverse .blowupTwo := by
  funext i j
  change _ = CalibrationSewingData.TwoBlowups.inverseMetric x y i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [tables, SurfaceReplay.TwoBlowups.tables,
      SurfaceReplay.TwoBlowups.values,
      SurfaceReplay.TwoBlowups.numerators,
      SurfaceReplay.TwoBlowups.denominators,
      CalibrationSewingData.TwoBlowups.inverseMetric, CalibrationSewingData.TwoBlowups.metricIndex,
      CalibrationSewingData.TwoBlowups.value, Matrix.cons_val, Matrix.of_apply]
  all_goals norm_num [Matrix.cons_val, Matrix.of_apply, tables, SurfaceReplay.TwoBlowups.tables,
      SurfaceReplay.TwoBlowups.values,
      SurfaceReplay.TwoBlowups.numerators,
      SurfaceReplay.TwoBlowups.denominators,
      CalibrationSewingData.TwoBlowups.inverseMetric, CalibrationSewingData.TwoBlowups.metricIndex,
      CalibrationSewingData.TwoBlowups.value, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one, Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

/-- The compact metric is the inverse metric of the original replay. -/
theorem metric_eq (X : SurfaceTarget) : (tables X).inverseMetric = metricInverse X := by
  cases X
  · exact metricPlane
  · exact metricOneBlowup
  · exact metricTwoBlowups

/-- Sum of the two endpoint terms and every positive-positive cut of the row. -/
def coefficient (X : SurfaceTarget) (r : Fin (rowCount X)) :
    Matrix (Index X) (Index X) Coefficient :=
  endpoint X r + ((-1 : Coefficient)^(row X r).power.val) • (endpoint X r).transpose +
    interior (row X r) (tables X).inverseMetric

end
end AxiomaticGW.GKM.CalibrationSewing
