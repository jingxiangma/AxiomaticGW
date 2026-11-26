/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.EquivariantCoefficients
public import AxiomaticGW.GKM.StateSpaceTransport

/-!
# Claim-bound certificates for exact GKM state-space tables

The caller holds the restriction matrix, Euler factors, tangent sums, and
ordinary tables fixed. Candidate data must prove every equality against
that request. The resulting certificates construct a genuine perfect
pairing and transported bilinear product. They certify classical localized
algebra, not a quantum product, CohFT classes, or numerical GW invariants.
-/

@[expose] public section

namespace AxiomaticGW.GKM.StateSpaceCertificate

open EquivariantCoefficients
open Matrix

/-- The independently specified classical state-space request. -/
structure Request (n : ℕ) where
  /-- Basis label designated as the unit. -/
  unitIndex : Fin n
  /-- Ordered basis restrictions in the chosen toric lifts. -/
  restrictions : Matrix (Fin n) (Fin n) Coefficient
  /-- Tangent Euler factors in the same fixed-point order. -/
  euler : Fin n → Coefficient
  /-- Sum of the two tangent characters at each fixed point. -/
  tangentSum : Fin n → Coefficient
  /-- Ordinary metric in the fixed rational surface basis. -/
  ordinaryMetric : Matrix (Fin n) (Fin n) ℚ
  /-- Ordinary cup-product coefficients in that basis. -/
  ordinaryProducts : Fin n → Fin n → Fin n → ℚ
  /-- Ordinary coordinates of the first Chern class. -/
  ordinaryC1 : Fin n → ℚ

/-- Exact candidate tables decoded from the version-one state-space bundle. -/
structure Tables (n : ℕ) where
  /-- Candidate basis-to-fixed-point restrictions. -/
  restrictions : Matrix (Fin n) (Fin n) Coefficient
  /-- Candidate fixed-point-to-basis inverse. -/
  inverse : Matrix (Fin n) (Fin n) Coefficient
  /-- Candidate tangent Euler factors. -/
  euler : Fin n → Coefficient
  /-- Candidate transformed metric. -/
  metric : Matrix (Fin n) (Fin n) Coefficient
  /-- Candidate inverse metric. -/
  inverseMetric : Matrix (Fin n) (Fin n) Coefficient
  /-- Candidate product coefficients. -/
  products : Fin n → Fin n → Fin n → Coefficient
  /-- Candidate first Chern coordinates, including equivariant scalar terms. -/
  c1 : Fin n → Coefficient

/-- Kernel proof obligations, indexed by the caller's request and candidate
tables. No digest, native arithmetic, or numerical sample proves acceptance. -/
structure Accepts {n : ℕ} (request : Request n) (tables : Tables n) : Prop where
  /-- The candidate restrictions are those of the fixed request. -/
  restrictions_eq : tables.restrictions = request.restrictions
  /-- The Euler factors are those of the fixed request. -/
  euler_eq : tables.euler = request.euler
  /-- Every actual Euler factor is nonzero in the exact coefficient field. -/
  euler_ne_zero : ∀ p, tables.euler p ≠ 0
  /-- The inverse is checked in the forward order. -/
  restrictions_inverse : tables.restrictions * tables.inverse = 1
  /-- The inverse is also checked in the reverse order. -/
  inverse_restrictions : tables.inverse * tables.restrictions = 1
  /-- The metric is the complete weighted fixed-point sum. -/
  metric_eq : tables.metric = tables.restrictions.transpose *
    Matrix.diagonal (fun p ↦ (tables.euler p)⁻¹) * tables.restrictions
  /-- The inverse metric uses the same Euler factors and inverse basis. -/
  inverseMetric_eq : tables.inverseMetric = tables.inverse *
    Matrix.diagonal tables.euler * tables.inverse.transpose
  /-- Products restrict to the product of the same two basis restrictions. -/
  products_eq : ∀ i j, tables.restrictions *ᵥ tables.products i j =
    tables.restrictions.col i * tables.restrictions.col j
  /-- The designated basis state restricts to the constant flat unit. -/
  unit_eq : tables.restrictions.col request.unitIndex = 1
  /-- First Chern coordinates reconstruct the independently specified tangent sum. -/
  c1_eq : tables.restrictions *ᵥ tables.c1 = request.tangentSum
  /-- Complete metric coefficients specialize to the requested ordinary metric. -/
  metric_specializes : ∀ i j, Specializes (tables.metric i j) (request.ordinaryMetric i j)
  /-- Complete product coefficients specialize to the requested ordinary product. -/
  products_specialize : ∀ i j k,
    Specializes (tables.products i j k) (request.ordinaryProducts i j k)
  /-- The equivariant Chern coordinates specialize to the requested ordinary class. -/
  c1_specializes : ∀ i, Specializes (tables.c1 i) (request.ordinaryC1 i)

namespace Accepts

variable {n : ℕ} {request : Request n} {tables : Tables n}

/-- Certified nonzero Euler factors provide the actual invertible weights. -/
noncomputable def eulerUnits (h : Accepts request tables) : Fin n → Coefficientˣ :=
  fun p ↦ Units.mk0 (tables.euler p) (h.euler_ne_zero p)

/-- The checked basis matrices define an actual state-space equivalence. -/
noncomputable def equivalence (h : Accepts request tables) :
    (Fin n → Coefficient) ≃ₗ[Coefficient] (Fin n → Coefficient) :=
  StateSpaceTransport.basisEquiv tables.restrictions tables.inverse
    h.restrictions_inverse h.inverse_restrictions

/-- The exported metric is the genuine pulled-back perfect pairing. -/
theorem metric_correct (h : Accepts request tables) (i j : Fin n) :
    ((FixedPointAlgebra.algebra h.eulerUnits).pairing.comap h.equivalence).form
      (Pi.single i 1) (Pi.single j 1) = tables.metric i j := by
  simp only [equivalence]
  rw [StateSpaceTransport.pairing_basis]
  simp only [StateSpaceTransport.metricMatrix, FixedPointAlgebra.metricMatrix,
    eulerUnits, Units.val_inv_eq_inv_val, Units.val_mk0, ← h.metric_eq]

/-- Both candidate metric tables are inverse, derived from accepted identities. -/
theorem metric_mul_inverse (h : Accepts request tables) :
    tables.metric * tables.inverseMetric = 1 := by
  have hm : tables.metric = StateSpaceTransport.metricMatrix h.eulerUnits
      tables.restrictions := by
    simpa only [StateSpaceTransport.metricMatrix, FixedPointAlgebra.metricMatrix,
      eulerUnits, Units.val_inv_eq_inv_val, Units.val_mk0] using h.metric_eq
  have hi : tables.inverseMetric = StateSpaceTransport.inverseMetricMatrix h.eulerUnits
      tables.inverse := by
    simpa only [StateSpaceTransport.inverseMetricMatrix, FixedPointAlgebra.inverseMetricMatrix,
      eulerUnits, Units.val_mk0] using h.inverseMetric_eq
  rw [hm, hi]
  exact StateSpaceTransport.metricMatrix_mul_inverse _ _ _
    h.restrictions_inverse h.inverse_restrictions

/-- Candidate coefficients are those of the proved transported product,
rather than componentwise multiplication on basis coordinates. -/
theorem product_correct (h : Accepts request tables) (i j : Fin n) :
    StateSpaceTransport.product h.equivalence (Pi.single i 1) (Pi.single j 1) =
      tables.products i j := by
  apply h.equivalence.injective
  rw [StateSpaceTransport.restriction_product]
  simp only [equivalence, StateSpaceTransport.basisEquiv_apply,
    Matrix.mulVec_single_one, h.products_eq]

/-- The original unit basis state is the transported flat unit. -/
theorem unit_correct (h : Accepts request tables) :
    StateSpaceTransport.unit h.equivalence = Pi.single request.unitIndex 1 := by
  apply h.equivalence.injective
  rw [StateSpaceTransport.restriction_unit]
  simp only [equivalence, StateSpaceTransport.basisEquiv_apply,
    Matrix.mulVec_single_one, h.unit_eq]

/-- A second proposed ordinary product value must equal the fixed request. -/
theorem ordinary_product_unique (h : Accepts request tables) (i j k : Fin n)
    (value : ℚ) (hv : Specializes (tables.products i j k) value) :
    value = request.ordinaryProducts i j k :=
  hv.unique (h.products_specialize i j k)

end Accepts

end AxiomaticGW.GKM.StateSpaceCertificate
