/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FixedPointAlgebra
public import AxiomaticGW.TFT.Correlator

/-!
# Canonical TFT formulas for the localized fixed-point Frobenius algebra

The Casimir is derived from the existing inverse-metric contraction identity.
Multiplying its two tensor legs gives the actual Frobenius handle element,
whose coordinate at a fixed point is the tangent Euler factor. Consequently
the existing all-genus correlator has its expected weighted fixed-point sum.

The formula retains inverse Euler times Euler to the genus power, including
genus zero and empty label types. These are the canonical algebraic TFT
correlators; no geometric localization identity or new CohFT law is assumed.
-/

@[expose] public section

namespace AxiomaticGW.GKM.FixedPointTFT

open scoped BigOperators
open TensorProduct FixedPointAlgebra

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The actual canonical Casimir is the inverse Euler-metric tensor. -/
theorem casimir_eq (euler : ι → Kˣ) :
    (algebra euler).casimir =
      ∑ p, (euler p : K) • ((Pi.single p 1) ⊗ₜ[K] (Pi.single p 1)) := by
  apply (algebra euler).pairing.tensorEndEquiv.injective
  apply LinearMap.ext
  intro a
  simp only [CommFrobeniusAlgebra.tensorEndEquiv_casimir, LinearMap.id_coe, id_eq,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    SymmetricPerfectPairing.tensorEndEquiv_tmul, smul_smul]
  calc
    a = ∑ p, ((euler p : K) * (algebra euler).pairing.form a (Pi.single p 1)) •
        Pi.single p 1 := expansion_from_pairing euler a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [(algebra euler).pairing.isSymm.eq a (Pi.single p 1)]

/-- The derived handle element is the function of tangent Euler factors. -/
theorem handleElement_eq (euler : ι → Kˣ) :
    (algebra euler).handleElement = fun p ↦ (euler p : K) := by
  rw [CommFrobeniusAlgebra.handleElement, casimir_eq]
  simp only [map_sum, map_smul, LinearMap.mul'_apply, ← Pi.single_mul, mul_one]
  exact (pi_eq_sum_univ' (fun p ↦ (euler p : K))).symm

/-- The canonical correlator retains the inverse Euler weight at every genus and arity. -/
theorem correlator_eq (euler : ι → Kˣ) (g : ℕ)
    {S : Type*} [Fintype S] (a : S → ι → K) :
    (algebra euler).correlator g S a =
      ∑ p, (↑((euler p)⁻¹) : K) * (euler p : K) ^ g * ∏ s, a s p := by
  rw [CommFrobeniusAlgebra.correlator_apply, handleElement_eq]
  change counit euler ((∏ s, a s) * (fun p ↦ (euler p : K)) ^ g) = _
  rw [counit_apply]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
  ac_rfl

/-- With unit insertions the genus-two TFT value is the sum of the Euler factors. -/
theorem correlator_two_unit (euler : ι → Kˣ) (S : Type*) [Fintype S] :
    (algebra euler).correlator 2 S (fun _ ↦ 1) = ∑ p, (euler p : K) := by
  rw [correlator_eq]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Pi.one_apply, Finset.prod_const_one, mul_one, pow_two]
  exact Units.inv_mul_cancel_left (euler p) (euler p : K)

end AxiomaticGW.GKM.FixedPointTFT
