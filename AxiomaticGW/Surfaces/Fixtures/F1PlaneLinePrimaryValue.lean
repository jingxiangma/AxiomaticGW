/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLinePrimary
public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineBPScalar

/-! # Absolute primary genus-two value at the pullback line

At the shifted source 2E+F, the four BP equations have zero combined
coefficient for each relevant first-descendant column. The original primary
pivot is six. All curve coordinates, marking orders, and divisor signs are
retained in the scalar comparison.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLine
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar SurfacePolynomialReduction
open SurfacePointBenchmarkCache BelorousskiPandharipande SurfaceGenusTwoBPFirstScalar

set_option Elab.async false
set_option maxRecDepth 20000

private def curve : Fin 5 → X.Curve := ![0,0,line,line,line]
private def remaining : Fin 5 → X.Curve := ![![2,1],![2,1],![1,0],![1,0],![1,0]]
private def insertion : Fin 5 → SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional 0, .hyperplane, .point, .exceptional 0]
private def count : Fin 5 → ℕ := ![0,0,3,2,3]
private def variableAt (c : Fin 5) : Variable X :=
  .inr (SurfaceFirstDescendant.query 2 (curve c) (insertion c) (count c))

private def rowAt (c : Fin 5) (a : Fin 3 → SurfaceBasisLabel X) :=
  row (variableAt c) (genusZero X) (remaining c) 3 a

private theorem rowAt_eq (c : Fin 5) (a : Fin 3 → SurfaceBasisLabel X) :
    rowAt c a = BelorousskiPandharipande.pointCoefficient X 3 (![2,1] : X.Curve) a
      (variableAt c) := by
  have hs : SurfaceGenusZero.variableCurve (variableAt c) + remaining c = ![2,1] := by
    fin_cases c <;> decide +kernel
  unfold rowAt
  rw [row_eq (variableAt c) (fun beta n ↦ SurfaceFirstDescendant.query_ne_points
    (curve c) beta (insertion c) (count c) n) _ (genusZero_eq X), hs]

private def mixed (c : Fin 5) :=
  3 / 2 * rowAt c ![.exceptional 0, .hyperplane, .hyperplane] -
    rowAt c ![.exceptional 0, .exceptional 0, .hyperplane] +
    1 / 2 * rowAt c ![.exceptional 0, .exceptional 0, .exceptional 0] -
    1 / 3 * rowAt c ![.hyperplane, .hyperplane, .hyperplane]

private theorem mixed_eq (c : Fin 5) :
    singletonCoefficient 0 (line, .primary) (variableAt c) = mixed c := by
  have he : X.effective.energy line = 3 := by decide +kernel
  have hs : line + X.exceptionalCurve 0 = ![2,1] := by decide +kernel
  have hd : X.planeDegree line = 1 := by decide +kernel
  simp only [singletonCoefficient, he, hs, hd, Nat.cast_one, mul_one, mixed, rowAt_eq]
  ring

set_option maxHeartbeats 1000000 in
-- The original four BP orbits use all six relabelings at each of five full columns.
private theorem mixed_value (c : Fin 5) : mixed c = 0 := by
  fin_cases c <;> decide +kernel

/-- Four primary point insertions in class E+F have reconstructed genus-two value zero. -/
theorem primary_value : value (line, .primary) = 0 := by
  have hc (c : Fin 5) := (mixed_eq c).trans (mixed_value c)
  have hp : singletonCoefficient 0 (line, .primary)
      (.inr ((Family.primary : Family X).query line)) = 6 := by
    rw [singletonCoefficient_eq, ← SurfaceGenusTwoBlowupOrderedCertificate.pivot_eq 0
      (line, .primary) (by change 0 < X.planeDegree line; decide +kernel)]
    decide +kernel
  have h := reduced_row (.primary : Family X)
  rw [Fin.sum_univ_four] at h
  change constant 0 (line,.primary) - singletonCoefficient _ _ (variableAt 0) / 960 -
    singletonCoefficient _ _ (variableAt 1) / 2880 +
    (singletonCoefficient _ _ (variableAt 2) * _ + singletonCoefficient _ _ (variableAt 3) * _ +
      singletonCoefficient _ _ (.inr ((Family.primary : Family X).query line)) *
        value (line,.primary) + singletonCoefficient _ _ (variableAt 4) * _) = 0 at h
  rw [primary_constant, hc 0, hc 1, hc 2, hc 3, hc 4, hp] at h
  linarith only [h]

end AxiomaticGW.F1PlaneLine
