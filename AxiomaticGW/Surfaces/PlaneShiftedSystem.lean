/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneHyperplaneRow
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The complete shifted plane genus-two coefficient block

The matrix is extracted from the full normalized BP equations, in HHP,
HPP, PPP order. Its columns are the primary, hyperplane descendant and point
descendant at degree d. At positive degree the determinant is 7776d, and every
other variable with a nonzero coefficient has strictly smaller degree.

These are algebraic coefficient and linear-system results. A recursive
invariant evaluator still needs the lower-degree reductions and finite seeds.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo

/-- The complete PPP coefficient on an arbitrary variable of positive degree d. -/
theorem normalized_plane_three_points_canonical (d : ℕ) (hd : 0 < d)
    (v : Variable .plane) (hv : SurfaceGenusZero.variableCurve v = ![d]) :
    RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d - 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.point, .point, .point] (3 * d - 1))) {v} =
      -18 * (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)) = v
        then 1 else 0) +
      18 * (d : ℚ) *
        (if Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)) = v
          then 1 else 0) := by
  have hc : SurfaceGenusZero.variableCurve v + ![1] =
      (![d + 1] : SurfaceTarget.plane.Curve) := by
    rw [hv]
    funext i
    fin_cases i
    rfl
  have hn : 3 * d - 1 + 1 = 3 * d := by omega
  rw [← pointCoefficient_eq_full, ← hc, ← planeRemainderPointCoefficient_eq,
    planeRemainderPointCoefficient_three_points_canonical]
  simp only [hv, Matrix.cons_val_zero, hn, ite_true]
  ring

/-- Every other variable in PPP has degree strictly below d. The primary
column itself is zero, so only the two descendant exclusions are needed. -/
theorem normalized_plane_three_points_lower (d : ℕ) (hd : 0 < d) (v : Variable .plane)
    (hH : Sum.inr (SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d)) ≠ v)
    (hP : Sum.inr (SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)) ≠ v)
    (hc : RationalTerms.coefficient (normalizedGenusTwoTerms .plane (3 * d - 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.point, .point, .point] (3 * d - 1))) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < d := by
  have hb := normalized_plane_two_points_degree_lt v (3 * d - 1) (d + 1)
    .point (Or.inr rfl) hc
  have hn : SurfaceGenusZero.variableCurve v 0 ≠ d := by
    intro he
    have hv : SurfaceGenusZero.variableCurve v = ![d] := by
      funext i
      fin_cases i
      exact he
    rw [normalized_plane_three_points_canonical d hd v hv] at hc
    simp only [if_neg hH, if_neg hP, mul_zero, add_zero, ne_eq,
      not_true_eq_false] at hc
  omega

/-- The three degree-d requests, ordered as primary, H descendant and P descendant. -/
def planeCanonicalQueries (d : ℕ) : Fin 3 → SurfaceQuery .plane :=
  ![SurfaceQuery.points .plane 2 ![d] (3 * d + 1),
    SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d),
    SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)]

/-- The original normalized HHP, HPP and PPP equations at source degree d+1. -/
def planeShiftedTerms (d : ℕ) : Fin 3 → RationalTerms (Variable .plane) :=
  ![normalizedGenusTwoTerms .plane (3 * d + 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .hyperplane, .point] (3 * d + 1)),
    normalizedGenusTwoTerms .plane (3 * d) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.hyperplane, .point, .point] (3 * d)),
    normalizedGenusTwoTerms .plane (3 * d - 1) ![d + 1] 0
      (SurfaceGenusZero.pointLabels ![.point, .point, .point] (3 * d - 1))]

/-- Extract the actual three canonical coefficients from each complete equation. -/
def planeShiftedMatrix (d : ℕ) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j ↦ RationalTerms.coefficient (planeShiftedTerms d i) {Sum.inr (planeCanonicalQueries d j)}

/-- Uniform identification of the full canonical coefficient block at positive degree. -/
theorem planeShiftedMatrix_eq (d : ℕ) (hd : 0 < d) :
    planeShiftedMatrix d =
      !![-108 * (d : ℚ), -27 * (d : ℚ) ^ 2 + 27 * (d : ℚ) + 12,
          27 * (d : ℚ) ^ 3 + 9 * (d : ℚ) ^ 2;
        -36, 12 - 36 * (d : ℚ), 36 * (d : ℚ) ^ 2;
        0, -18, 18 * (d : ℚ)] := by
  have h0 := normalized_plane_two_hyperplanes_point_row d
  have h1 := normalized_plane_hyperplane_two_points_row d
  have h2 := normalized_plane_three_points_row d hd
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst h0
  · exact congrArg (fun x ↦ x.2.1) h0
  · exact congrArg (fun x ↦ x.2.2) h0
  · exact congrArg Prod.fst h1
  · exact congrArg (fun x ↦ x.2.1) h1
  · exact congrArg (fun x ↦ x.2.2) h1
  · exact congrArg Prod.fst h2
  · exact congrArg (fun x ↦ x.2.1) h2
  · exact congrArg (fun x ↦ x.2.2) h2

/-- Determinant of the matrix extracted from the three complete equations. -/
theorem planeShiftedMatrix_det (d : ℕ) (hd : 0 < d) :
    (planeShiftedMatrix d).det = 7776 * (d : ℚ) := by
  rw [planeShiftedMatrix_eq d hd, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one]
  ring

/-- The canonical block is nonsingular at every positive degree. -/
theorem planeShiftedMatrix_det_ne_zero (d : ℕ) (hd : 0 < d) :
    (planeShiftedMatrix d).det ≠ 0 := by
  rw [planeShiftedMatrix_det d hd]
  exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))

/-- Every prescribed right-hand side determines exactly one canonical block.
This does not assume or construct the lower-degree invariant data. -/
theorem planeShiftedMatrix_existsUnique (d : ℕ) (hd : 0 < d) (b : Fin 3 → ℚ) :
    ∃! x : Fin 3 → ℚ, (planeShiftedMatrix d).mulVec x = b := by
  have hu : IsUnit (planeShiftedMatrix d) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (planeShiftedMatrix_det_ne_zero d hd))
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu b
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact Matrix.mulVec_injective_iff_isUnit.mpr hu (hy.trans hx.symm)

/-- In all three complete equations, every noncanonical surviving variable
has strictly smaller degree. This includes unreduced ancestor variables. -/
theorem planeShiftedTerms_lower (d : ℕ) (hd : 0 < d) (i : Fin 3) (v : Variable .plane)
    (h : ∀ j, Sum.inr (planeCanonicalQueries d j) ≠ v)
    (hc : RationalTerms.coefficient (planeShiftedTerms d i) {v} ≠ 0) :
    SurfaceGenusZero.variableCurve v 0 < d := by
  fin_cases i
  · exact normalized_plane_two_hyperplanes_point_lower d v (h 0) (h 1) (h 2) hc
  · exact normalized_plane_hyperplane_two_points_lower d v (h 0) (h 1) (h 2) hc
  · exact normalized_plane_three_points_lower d hd v (h 1) (h 2) hc

/-- Executable rational solution of the canonical block at positive degree.
Degree zero is reserved for initial data; the solution theorem requires d>0. -/
def planeShiftedSolve (d : ℕ) (b : Fin 3 → ℚ) : Fin 3 → ℚ :=
  let D := (d : ℚ)
  ![b 0 / 36 - (3 * D + 1) * b 1 / 36 + D * (3 * D + 1) * b 2 / 24,
    b 0 / 12 - D * b 1 / 4 + D * (9 * D - 1) * b 2 / 24,
    b 0 / (12 * D) - b 1 / 4 + (27 * D ^ 2 - 3 * D + 4) * b 2 / (72 * D)]

/-- The executable solution satisfies the actual coefficient equations. -/
theorem planeShiftedSolve_spec (d : ℕ) (hd : 0 < d) (b : Fin 3 → ℚ) :
    (planeShiftedMatrix d).mulVec (planeShiftedSolve d b) = b := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  rw [planeShiftedMatrix_eq d hd]
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, planeShiftedSolve,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    field_simp [hd'] <;> ring_nf <;> rfl

/-- Any solution of the complete canonical coefficient block is the computed one. -/
theorem planeShiftedSolve_unique (d : ℕ) (hd : 0 < d) (b x : Fin 3 → ℚ)
    (hx : (planeShiftedMatrix d).mulVec x = b) : x = planeShiftedSolve d b := by
  obtain ⟨y, _, hy⟩ := planeShiftedMatrix_existsUnique d hd b
  exact (hy x hx).trans (hy _ (planeShiftedSolve_spec d hd b)).symm

end AxiomaticGW.BelorousskiPandharipande
