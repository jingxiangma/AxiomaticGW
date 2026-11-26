/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleLineBPEquation
public import AxiomaticGW.Surfaces.GenusTwoFirstCoefficients

/-! # The point descendant at 2L is half the hyperplane descendant

The original point row has sixteen lower-genus primary sources. Each vanishes with its
extra point. The four original genus-two diagrams also give zero on each of the three
nonzero divisor seeds at the constant class.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleLineBP
open SurfaceGenusTwo SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar
open SurfacePolynomialReduction BelorousskiPandharipande SurfacePointBenchmarkCache
open BlowupTwoDoubleLine (curve)
open BlowupTwoLineBP (canonicalFamily)

private theorem triple : (![.hyperplane, .hyperplane, .hyperplane] : Fin 3 → SurfaceBasisLabel X)
    = fun _ ↦ .hyperplane := by
  funext i
  fin_cases i <;> rfl

/-- The sixteen signed lower contributions before multiplying by the six identical permutations. -/
def lowerTerm (j : Fin 16) : ℚ :=
  rawPaperCoefficient (Fin.natAdd 4 j) *
    SurfaceGenusOne.primaryGraphDimensionEval X (genusZero X) (genusOne X)
      (paperTerm (Fin.natAdd 4 j)).1 curve 1 (fun _ ↦ .hyperplane)

set_option Elab.async false
set_option maxRecDepth 32768

set_option maxHeartbeats 1600000 in
-- Each primary graph distributes its point among its actual effective splittings.
theorem lower_zero (j : Fin 16) : lowerTerm j = 0 := by
  fin_cases j <;> decide +kernel

/-- The constant in the original unshifted equation before any genus-two terms. -/
theorem point_constant_zero : constant 0 (curve, .point) = 0 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (curve, .point)
    (genusZero X) (genusOne X) (genusZero_eq X) (genusOne_eq X)]
  change lowerPointConstantWithPrimary X (genusZero X) (genusOne X)
    1 curve ![.hyperplane, .hyperplane, .hyperplane] = 0
  rw [triple, lowerPointConstantWithPrimary_eq_six_primaryGraphSum]
  change 6 * (∑ j, lowerTerm j) = 0
  simp only [lower_zero, Finset.sum_const_zero, mul_zero]

def seedDivisor : Fin 3 → SurfaceBasisLabel X := ![.hyperplane, .exceptional 0, .exceptional 1]
def baseColumn (j : Fin 3) : Variable X :=
  .inr (SurfaceFirstDescendant.query 2 0 (seedDivisor j) 0)

/-- The genus-two coefficient diagrams on the true remaining class 2L. -/
def baseDiagram (j : Fin 3) (k : Fin 4) : ℚ :=
  remainderPointCoefficient X (baseColumn j) (firstCoefficientVertex X 0 (seedDivisor j) 0)
    (paperCotangentTerm (Fin.castAdd 16 k)) curve 1 (fun _ ↦ .hyperplane)

set_option maxHeartbeats 1200000 in
-- Check the individual genus-two diagrams of each full class-zero divisor column.
theorem base_zero (j : Fin 3) (k : Fin 4) : baseDiagram j k = 0 := by
  fin_cases j <;> fin_cases k <;> decide +kernel

theorem base_coefficient_zero (j : Fin 3) :
    singletonCoefficient 0 (curve, .point) (baseColumn j) = 0 := by
  change BelorousskiPandharipande.pointCoefficient X 1 curve
    ![.hyperplane, .hyperplane, .hyperplane] (baseColumn j) = 0
  rw [triple, pointCoefficient_eq_six_paperSum]
  apply Finset.sum_eq_zero
  intro k _
  have hb := remainderPointCoefficient_eq X (baseColumn j) _
    (firstCoefficientVertex_eq (X := X) 0 (seedDivisor j) 0)
    (paperCotangentTerm (Fin.castAdd 16 k)) curve 1 (fun _ ↦ .hyperplane)
  change baseDiagram j k = SurfaceGenusTwo.pointCoefficient X (baseColumn j) _
    (0 + curve) 1 _ at hb
  rw [zero_add] at hb
  rw [← hb, base_zero, mul_zero, mul_zero]

/-- Cancellation here is termwise in the original three divisor seed columns. -/
theorem residual_zero : residual = 0 := by
  rw [residual, point_constant_zero, zero_add, Fin.sum_univ_five]
  change singletonCoefficient 0 (curve, .point) (baseColumn 0) * _ + _ * 0 + _ * 0 +
    singletonCoefficient 0 (curve, .point) (baseColumn 1) * _ +
    singletonCoefficient 0 (curve, .point) (baseColumn 2) * _ = 0
  simp only [base_coefficient_zero, mul_zero, zero_mul, add_zero]

/-- Exact relation of the original canonical point and hyperplane descendants at 2L. -/
theorem point_eq_half_hyperplane :
    actual (curve, .point) = actual (curve, .hyperplane) / 2 := by
  have h := point_equation
  rw [residual_zero, add_zero] at h
  linarith only [h]

end AxiomaticGW.BlowupTwoDoubleLineBP
