/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Frobenius.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Matrix.Diagonal

/-!
# Localized fixed-point Frobenius algebra

The state space is the existing pointwise algebra `ι → K`. Invertible Euler
factors determine the trace `a ↦ ∑ p, a p / euler p`, its perfect metric,
and its inverse metric. The coordinate idempotents give the split classical
algebra consumed by GKM input exchange. This does not construct a quantum
product or prove a geometric localization or CohFT comparison theorem.
-/

@[expose] public section

namespace AxiomaticGW.GKM.FixedPointAlgebra

open scoped BigOperators

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Exact localization trace with inverse Euler weights. -/
noncomputable def counit (euler : ι → Kˣ) : (ι → K) →ₗ[K] K :=
  ∑ p, (↑((euler p)⁻¹) : K) • LinearMap.proj p

/-- The trace evaluates to the weighted sum of fixed-point restrictions. -/
theorem counit_apply (euler : ι → Kˣ) (a : ι → K) :
    counit euler a = ∑ p, (↑((euler p)⁻¹) : K) * a p := by
  simp only [counit, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

variable [DecidableEq ι]

/-- A coordinate state has trace equal to its inverse Euler weight. -/
theorem counit_single (euler : ι → Kˣ) (i : ι) (a : K) :
    counit euler (Pi.single i a) = (↑((euler i)⁻¹) : K) * a := by
  rw [counit_apply]
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Testing against a coordinate idempotent extracts the weighted coordinate. -/
theorem tracePairing_single_right (euler : ι → Kˣ) (a : ι → K) (i : ι) :
    tracePairing (counit euler) a (Pi.single i 1) =
      (↑((euler i)⁻¹) : K) * a i := by
  rw [tracePairing_apply]
  have h : a * Pi.single i 1 = Pi.single i (a i) := by
    ext j
    by_cases hij : i = j
    · subst j
      simp only [Pi.mul_apply, Pi.single_eq_same, mul_one]
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne (Ne.symm hij), mul_zero]
  rw [h, counit_single]

/-- The localization trace is perfect on the finite pointwise algebra. -/
noncomputable def algebra (euler : ι → Kˣ) : CommFrobeniusAlgebra K (ι → K) where
  counit := counit euler
  isPerfPair := by
    have hinj : Function.Injective (tracePairing (counit euler)) := by
      intro a b h
      ext i
      have hi := DFunLike.congr_fun h (Pi.single i 1)
      rw [tracePairing_single_right, tracePairing_single_right] at hi
      exact mul_left_cancel₀ (Units.ne_zero ((euler i)⁻¹)) hi
    apply LinearMap.IsPerfPair.of_injective hinj
    intro a b h
    apply hinj
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun h x
    simpa only [LinearMap.flip_apply, tracePairing_apply, mul_comm] using hx

/-- The bundled Frobenius metric retains the exact inverse Euler factor. -/
theorem algebra_pairing_single_right (euler : ι → Kˣ) (a : ι → K) (i : ι) :
    (algebra euler).pairing.form a (Pi.single i 1) =
      (↑((euler i)⁻¹) : K) * a i := tracePairing_single_right euler a i

/-- The metric in the coordinate-idempotent basis. -/
def metricMatrix (euler : ι → Kˣ) : Matrix ι ι K :=
  Matrix.diagonal (fun p ↦ (↑((euler p)⁻¹) : K))

/-- The inverse metric is derived from the same Euler factors. -/
def inverseMetricMatrix (euler : ι → Kˣ) : Matrix ι ι K :=
  Matrix.diagonal (fun p ↦ (↑(euler p) : K))

/-- Both metric tables compose to the identity; no independent inverse is assumed. -/
theorem metricMatrix_mul_inverse (euler : ι → Kˣ) :
    metricMatrix euler * inverseMetricMatrix euler = 1 := by
  simp only [metricMatrix, inverseMetricMatrix, Matrix.diagonal_mul_diagonal,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.diagonal_one]

/-- The reverse matrix product is also the identity. -/
theorem inverseMetricMatrix_mul_metric (euler : ι → Kˣ) :
    inverseMetricMatrix euler * metricMatrix euler = 1 := by
  simp only [metricMatrix, inverseMetricMatrix, Matrix.diagonal_mul_diagonal,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.diagonal_one]

/-- The diagonal matrix is the actual Frobenius metric in this basis. -/
theorem algebra_pairing_idempotents (euler : ι → Kˣ) (i j : ι) :
    (algebra euler).pairing.form (Pi.single i 1) (Pi.single j 1) =
      metricMatrix euler i j := by
  rw [algebra_pairing_single_right]
  by_cases h : i = j
  · subst j
    simp only [Pi.single_eq_same, mul_one, metricMatrix, Matrix.diagonal_apply_eq]
  · simp only [Pi.single_eq_of_ne (Ne.symm h), mul_zero, metricMatrix,
      Matrix.diagonal_apply_ne _ h]

/-- Inverse-metric contraction against coordinate idempotents recovers any
state. This is the finite algebraic normalization needed by GKM exchange. -/
theorem expansion_from_pairing (euler : ι → Kˣ) (a : ι → K) :
    a = ∑ p, ((euler p : K) * (algebra euler).pairing.form a (Pi.single p 1)) •
      Pi.single p 1 := by
  calc
    a = ∑ p, a p • Pi.single p 1 := pi_eq_sum_univ' a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [algebra_pairing_single_right]
      congr 1
      exact (Units.mul_inv_cancel_left (euler p) (a p)).symm

end AxiomaticGW.GKM.FixedPointAlgebra
