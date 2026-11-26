/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FixedPointAlgebra
public import AxiomaticGW.CohFT.Transport
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# GKM basis, metric, and product transport

Forward and inverse restriction matrices must be proved inverse in Lean.
They then define a linear equivalence, the transformed Euler metric and its
inverse, and a bilinear product with its own transported unit. The same
equivalence is consumed by `CohFT.comap` for a supplied class-valued theory.

The coefficient vectors' existing pointwise ring structure is not their
transported surface product. No competing global ring instance is installed.
This module does not certify the Python input bundle, ordinary specialization,
quantum multiplication, or a geometric localization comparison.
-/

@[expose] public section

namespace AxiomaticGW.GKM.StateSpaceTransport
open Matrix
open scoped BigOperators
variable {K ι κ : Type*} [Field K]

section Matrices
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Two checked inverse restriction matrices give the state-to-fixed-point
linear equivalence. The forward map is `B`, not the supplied inverse `C`. -/
def basisEquiv (B : Matrix ι κ K) (C : Matrix κ ι K)
    (hBC : B * C = 1) (hCB : C * B = 1) : (κ → K) ≃ₗ[K] (ι → K) :=
  Matrix.toLin'OfInv hCB hBC

/-- Basis states restrict by the supplied forward matrix. -/
theorem basisEquiv_apply (B : Matrix ι κ K) (C : Matrix κ ι K)
    (hBC : B * C = 1) (hCB : C * B = 1) (a : κ → K) :
    basisEquiv B C hBC hCB a = B *ᵥ a := rfl

/-- Fixed-point values return through the supplied inverse matrix. -/
theorem basisEquiv_symm_apply (B : Matrix ι κ K) (C : Matrix κ ι K)
    (hBC : B * C = 1) (hCB : C * B = 1) (a : ι → K) :
    (basisEquiv B C hBC hCB).symm a = C *ᵥ a := rfl

/-- The metric obtained by transporting the inverse Euler diagonal. -/
def metricMatrix (euler : ι → Kˣ) (B : Matrix ι κ K) : Matrix κ κ K :=
  B.transpose * FixedPointAlgebra.metricMatrix euler * B

/-- The inverse metric obtained by transporting the Euler diagonal. -/
def inverseMetricMatrix (euler : ι → Kˣ) (C : Matrix κ ι K) : Matrix κ κ K :=
  C * FixedPointAlgebra.inverseMetricMatrix euler * C.transpose

/-- Exact basis transport preserves the metric inverse on both sides. -/
theorem metricMatrix_mul_inverse (euler : ι → Kˣ)
    (B : Matrix ι κ K) (C : Matrix κ ι K) (hBC : B * C = 1) (hCB : C * B = 1) :
    metricMatrix euler B * inverseMetricMatrix euler C = 1 := by
  unfold metricMatrix inverseMetricMatrix
  calc
    (B.transpose * FixedPointAlgebra.metricMatrix euler * B) *
        (C * FixedPointAlgebra.inverseMetricMatrix euler * C.transpose) =
      B.transpose * (FixedPointAlgebra.metricMatrix euler * (B * C) *
        FixedPointAlgebra.inverseMetricMatrix euler) * C.transpose := by
          simp only [Matrix.mul_assoc]
    _ = B.transpose * C.transpose := by
      rw [hBC, Matrix.mul_one, FixedPointAlgebra.metricMatrix_mul_inverse, Matrix.mul_one]
    _ = 1 := by rw [← Matrix.transpose_mul, hCB, Matrix.transpose_one]

/-- The reverse metric product is also the identity. -/
theorem inverseMetricMatrix_mul_metric (euler : ι → Kˣ)
    (B : Matrix ι κ K) (C : Matrix κ ι K) (hBC : B * C = 1) (hCB : C * B = 1) :
    inverseMetricMatrix euler C * metricMatrix euler B = 1 := by
  unfold metricMatrix inverseMetricMatrix
  calc
    (C * FixedPointAlgebra.inverseMetricMatrix euler * C.transpose) *
        (B.transpose * FixedPointAlgebra.metricMatrix euler * B) =
      C * (FixedPointAlgebra.inverseMetricMatrix euler * (C.transpose * B.transpose) *
        FixedPointAlgebra.metricMatrix euler) * B := by
          simp only [Matrix.mul_assoc]
    _ = C * B := by
      rw [← Matrix.transpose_mul, hBC, Matrix.transpose_one, Matrix.mul_one,
        FixedPointAlgebra.inverseMetricMatrix_mul_metric, Matrix.mul_one]
    _ = 1 := hCB

/-- The transported table is the actual pulled-back perfect pairing. -/
theorem pairing_basis (euler : ι → Kˣ) (B : Matrix ι κ K) (C : Matrix κ ι K)
    (hBC : B * C = 1) (hCB : C * B = 1) (i j : κ) :
    ((FixedPointAlgebra.algebra euler).pairing.comap (basisEquiv B C hBC hCB)).form
        (Pi.single i 1) (Pi.single j 1) = metricMatrix euler B i j := by
  rw [SymmetricPerfectPairing.comap_apply,
    basisEquiv_apply, basisEquiv_apply, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    CommFrobeniusAlgebra.pairing_apply]
  change FixedPointAlgebra.counit euler (B.col i * B.col j) = metricMatrix euler B i j
  rw [FixedPointAlgebra.counit_apply, metricMatrix, Matrix.mul_apply]
  simp only [FixedPointAlgebra.metricMatrix,
    Matrix.transpose_apply, Matrix.mul_diagonal, Pi.mul_apply, Matrix.col_apply]
  apply Finset.sum_congr rfl
  intro p _
  ring

end Matrices

/-- Transport pointwise fixed-point multiplication as a bilinear map.
This does not install pointwise multiplication on the new coordinates. -/
def product (e : (κ → K) ≃ₗ[K] (ι → K)) :
    (κ → K) →ₗ[K] (κ → K) →ₗ[K] (κ → K) :=
  ((LinearMap.mul K (ι → K)).compl₁₂ e.toLinearMap e.toLinearMap).compr₂ e.symm.toLinearMap

/-- Multiplication is performed after restriction, then returned to the basis. -/
theorem product_apply (e : (κ → K) ≃ₗ[K] (ι → K)) (a b : κ → K) :
    product e a b = e.symm (e a * e b) := rfl

/-- Restricting the transported product recovers the fixed-point product. -/
theorem restriction_product (e : (κ → K) ≃ₗ[K] (ι → K)) (a b : κ → K) :
    e (product e a b) = e a * e b := e.apply_symm_apply _

/-- The new unit is the inverse image of the constant fixed-point function. -/
def unit (e : (κ → K) ≃ₗ[K] (ι → K)) : κ → K := e.symm 1

/-- The transported unit restricts to the constant function one. -/
theorem restriction_unit (e : (κ → K) ≃ₗ[K] (ι → K)) : e (unit e) = 1 :=
  e.apply_symm_apply _

/-- The transported bilinear product is associative. -/
theorem product_assoc (e : (κ → K) ≃ₗ[K] (ι → K)) (a b c : κ → K) :
    product e (product e a b) c = product e a (product e b c) := by
  apply e.injective
  simp only [restriction_product, mul_assoc]

/-- The transported bilinear product is commutative. -/
theorem product_comm (e : (κ → K) ≃ₗ[K] (ι → K)) (a b : κ → K) :
    product e a b = product e b a := by
  apply e.injective
  simp only [restriction_product, mul_comm]

/-- The transported unit is an identity for the bilinear product. -/
theorem product_unit_left (e : (κ → K) ≃ₗ[K] (ι → K)) (a : κ → K) :
    product e (unit e) a = a := by
  apply e.injective
  simp only [restriction_product, restriction_unit, one_mul]

/-- The transported metric retains Frobenius invariance. -/
theorem pairing_product [Fintype ι] [DecidableEq ι]
    (euler : ι → Kˣ) (e : (κ → K) ≃ₗ[K] (ι → K))
    (a b c : κ → K) :
    ((FixedPointAlgebra.algebra euler).pairing.comap e).form (product e a b) c =
      ((FixedPointAlgebra.algebra euler).pairing.comap e).form a (product e b c) := by
  simp only [SymmetricPerfectPairing.comap_apply, restriction_product]
  exact (FixedPointAlgebra.algebra euler).pairing_assoc _ _ _

end AxiomaticGW.GKM.StateSpaceTransport
