/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeTwoRawRelation
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Ordinary specialization of the genus-two degree-zero unit strata packet

Each decorated-graph coordinate of the saved GKM/admcycles candidate has a
polynomial representative after summing all fixed points, ordered Hodge pairs,
and homogeneous components. At zero torus weights the result is a rational
cycle on the free strata module of genus two with one marking. For the plane
and its one- and two-point blowups the multipliers of the same sixteen-column
degree-two packet are nine, eight and seven.

The pinned producer integrates contracted-vertex Hodge monomials. The class
input here is the saved pre-integration reconstruction of those factors.
Geometric identification with the stabilized virtual class is a separate
comparison.
-/

@[expose] public section
namespace AxiomaticGW.GKM.HodgeDegreeZeroStrataSpecialization
open EquivariantCoefficients HodgeDegreeZeroRawAssembly AdmcyclesHodgeStrataCandidates
open AdmcyclesHodgeStrataNormalization HodgeDegreeZeroFullCoefficientReplay

noncomputable section

/-- Decorated columns of the genus-two one-marked packet. -/
abbrev Stratum := TautologicalStratum 2 (Fin 1)

private def coordinate (s : Stratum) : StrataModule 2 (Fin 1) →+ Coefficient :=
  (Rat.castHom Coefficient).toAddMonoidHom.comp (Finsupp.applyAddHom s)

/-- A coefficient of the entire finite localization sum, retaining each occurrence. -/
def localizedCoefficient {ι : Type*} [Fintype ι] (coeff : ι → Fin 3 → Fin 3 → Coefficient)
    (s : Stratum) : Coefficient :=
  ∑ p, ∑ a, ∑ b, ∑ d : Fin 5, coeff p a b * (rawComponent a b d s : Coefficient)

private theorem collected {ι : Type*} [Fintype ι] (c : ι → Fin 3 → Fin 3 → Coefficient)
    (s : Stratum) :
    localizedCoefficient c s =
      (∑ p, c p 0 0) * coordinate s raw00Degree0 +
      (∑ p, (c p 0 1 + c p 1 0)) * coordinate s raw01Degree1 +
      (∑ p, (c p 0 2 + c p 2 0)) * coordinate s raw02Degree2 +
      (∑ p, c p 1 1) * coordinate s raw11Degree2 +
      (∑ p, (c p 1 2 + c p 2 1)) * coordinate s raw12Degree3 +
      (∑ p, c p 2 2) * coordinate s raw22Degree4 := by
  change (∑ p, ∑ a, ∑ b, ∑ d : Fin 5, c p a b * coordinate s (rawComponent a b d)) = _
  simp only [← Finset.mul_sum, ← map_sum, sum_rawComponent, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, raw_single_factor_one_symm, raw_single_factor_two_symm,
    ← AdmcyclesHodgeStrataIsomorphisms.raw_ordered_degree3_equal,
    Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  abel

/-- Each target uses its actual decoded fixed-point table. -/
def packet (X : SurfaceTarget) (s : Stratum) : Coefficient :=
  match X with
  | .plane => localizedCoefficient Plane.coefficients s
  | .hirzebruchOne => localizedCoefficient OneBlowup.coefficients s
  | .blowupTwo => localizedCoefficient TwoBlowups.coefficients s

/-- The ordinary representative in the free rational strata module. -/
def ordinary (X : SurfaceTarget) : StrataModule 2 (Fin 1) :=
  (9 - (X.blowups : ℚ)) • raw02Degree2

/-- Polynomial coefficient of the undecorated unit stratum. -/
def leadingCharacter (X : SurfaceTarget) : Polynomial :=
  let q := MvPolynomial.X (0 : Fin 2) ^ 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2
  match X with
  | .plane => q
  | .hirzebruchOne => 0
  | .blowupTwo => -q

/-- A denominator-free representative of a complete decorated-graph coordinate. -/
def regularCoordinate (X : SurfaceTarget) (s : Stratum) : Polynomial :=
  leadingCharacter X * MvPolynomial.C (raw00Degree0 s) + MvPolynomial.C (ordinary X s)

/-- Polynomial regularity at each raw stratum follows from the full ordered input. -/
theorem packet_eq_regular (X : SurfaceTarget) (s : Stratum) :
    packet X s = embed (regularCoordinate X s) := by
  have ht : coordinate s raw11Degree2 = 2 * coordinate s raw02Degree2 := by
    rw [HodgeDegreeTwoRawRelation.raw_degree_two_equal, two_smul, map_add, two_mul]
  have hc (v : StrataModule 2 (Fin 1)) : coordinate s v = (v s : Coefficient) := rfl
  cases X
  all_goals rw [packet, collected]
  all_goals first
    | rw [HodgeDegreeZeroRegularity.Plane.sum_constant,
        HodgeDegreeZeroRegularity.Plane.sum_lambda1,
        HodgeDegreeZeroRegularity.Plane.sum_lambda2,
        HodgeDegreeZeroRegularity.Plane.sum_lambda1Squared,
        HodgeDegreeZeroRegularity.Plane.sum_mixed,
        HodgeDegreeZeroRegularity.Plane.sum_lambda2Squared]
    | rw [HodgeDegreeZeroRegularity.OneBlowup.sum_constant,
        HodgeDegreeZeroRegularity.OneBlowup.sum_lambda1,
        HodgeDegreeZeroRegularity.OneBlowup.sum_lambda2,
        HodgeDegreeZeroRegularity.OneBlowup.sum_lambda1Squared,
        HodgeDegreeZeroRegularity.OneBlowup.sum_mixed,
        HodgeDegreeZeroRegularity.OneBlowup.sum_lambda2Squared]
    | rw [HodgeDegreeZeroRegularity.TwoBlowups.sum_constant,
        HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda1,
        HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda2,
        HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda1Squared,
        HodgeDegreeZeroRegularity.TwoBlowups.sum_mixed,
        HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda2Squared]
  all_goals
    rw [ht]
    simp only [hc, regularCoordinate, leadingCharacter, ordinary, SurfaceTarget.blowups,
      map_add, map_mul, map_pow, map_sub, map_neg, map_zero, embed_X_zero, embed_X_one, embed_C,
      Finsupp.smul_apply, smul_eq_mul, Rat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Rat.cast_one]
    ring

/-- The specialization is homogeneous of codimension two for all three surfaces. -/
theorem ordinary_mem_degree (X : SurfaceTarget) : ordinary X ∈ StrataModule.degree 2 :=
  (StrataModule.degree 2).smul_mem _ raw_0_2_degree2_mem_degree

private theorem raw_0_2_mass :
    Finsupp.linearCombination ℚ (fun _ : Stratum ↦ (1 : ℚ)) raw02Degree2 = 13 / 1152 := by
  simp only [raw02Degree2, RelationCertificate.interpret_apply, map_sum, map_smul,
    StrataModule.basis, Finsupp.linearCombination_single, smul_eq_mul, mul_one]
  decide +kernel

/-- Its coefficient sum detects a nonzero element of the free rational strata module. -/
theorem ordinary_ne_zero (X : SurfaceTarget) : ordinary X ≠ 0 := by
  intro h
  have he := congrArg (Finsupp.linearCombination ℚ (fun _ : Stratum ↦ (1 : ℚ))) h
  rw [ordinary, map_smul, raw_0_2_mass, map_zero, smul_eq_mul] at he
  cases X <;> norm_num [SurfaceTarget.blowups] at he

/-- Only the whole coefficient at a stratum is specialized to zero torus weights. -/
theorem packet_specializes (X : SurfaceTarget) (s : Stratum) :
    Specializes (packet X s) (ordinary X s) := by
  have hz : atZero (leadingCharacter X) = 0 := by
    cases X <;> simp only [leadingCharacter, atZero, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, MvPolynomial.eval₂Hom_X', Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero, add_zero, neg_zero]
  have he : atZero (regularCoordinate X s) = ordinary X s := by
    rw [regularCoordinate, map_add, map_mul, hz, zero_mul, zero_add]
    exact MvPolynomial.eval₂Hom_C _ _ _
  rw [← he]
  exact specializes_of_eq_polynomial _ (packet_eq_regular X s)

/-- These coordinate comparisons specify one ordinary cycle uniquely. -/
theorem ordinary_unique (X : SurfaceTarget) (v : StrataModule 2 (Fin 1))
    (h : ∀ s, Specializes (packet X s) (v s)) : v = ordinary X := by
  ext s
  exact (h s).unique (packet_specializes X s)

end

end AxiomaticGW.GKM.HodgeDegreeZeroStrataSpecialization
