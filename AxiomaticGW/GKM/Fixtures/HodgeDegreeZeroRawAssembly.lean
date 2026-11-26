/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRegularity
public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataIsomorphisms

/-!
# Complete raw assembly after fixed-point cancellation

The existing assembly retains all 45 raw components and every actual ordered
coefficient. Linearity and the accepted raw mixed-pair graph isomorphisms reduce
its complete fixed-point sum to the actual degree-zero and degree-two expressions.

The raw (1,1) and (0,2) expressions remain exactly their decoded strata sums.
No multiplication rule, geometric Hodge interpretation, GRR formula, GW class,
ordinary cohomology comparison or CohFT law is asserted. The result holds for
every existing realization, without scalar projection or fundamental normalization.
-/

@[expose] public section

set_option autoImplicit false

namespace AxiomaticGW.GKM.HodgeDegreeZeroRawAssembly

open AdmcyclesHodgeStrataCandidates AdmcyclesHodgeStrataNormalization
open EquivariantCoefficients Matrix
open scoped BigOperators

universe u

noncomputable section

private theorem interpret_empty
    (columns : Fin 0 → TautologicalStratum 2 (Fin 1))
    (coordinates : RelationCertificate.Coordinates 0) :
    RelationCertificate.interpret columns coordinates = 0 := by
  rw [RelationCertificate.interpret_apply]
  exact Fin.sum_univ_zero _

/-- All 36 empty components vanish; each of the nine nonempty source sums is retained. -/
theorem sum_rawComponent (a b : Fin 3) :
    (∑ d : Fin 5, rawComponent a b d) =
      ![![raw00Degree0, raw01Degree1, raw02Degree2],
        ![raw10Degree1, raw11Degree2, raw12Degree3],
        ![raw20Degree2, raw21Degree3, raw22Degree4]] a b := by
  fin_cases a <;> fin_cases b
  all_goals
    simp only [rawComponent, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      Fin.isValue,
      raw00Degree1, raw00Degree2, raw00Degree3,
      raw00Degree4, raw01Degree0, raw01Degree2,
      raw01Degree3, raw01Degree4, raw02Degree0,
      raw02Degree1, raw02Degree3, raw02Degree4,
      raw10Degree0, raw10Degree2, raw10Degree3,
      raw10Degree4, raw11Degree0, raw11Degree1,
      raw11Degree3, raw11Degree4, raw12Degree0,
      raw12Degree1, raw12Degree2, raw12Degree4,
      raw20Degree0, raw20Degree1, raw20Degree3,
      raw20Degree4, raw21Degree0, raw21Degree1,
      raw21Degree2, raw21Degree4, raw22Degree0,
      raw22Degree1, raw22Degree2, raw22Degree3,
      interpret_empty, add_zero, zero_add]

/-- The two single-factor pairs already have identical actual columns and coordinates. -/
theorem raw_single_factor_one_symm : raw10Degree1 = raw01Degree1 := rfl

/-- The second single-factor pair also has identical actual columns and coordinates. -/
theorem raw_single_factor_two_symm : raw20Degree2 = raw02Degree2 := rfl

variable {K : Type u} [Field K] [Algebra ℚ K]
  {C : StableCurveCohomology K} {ι : Type*} [Fintype ι]

attribute [local instance] strataRealizationModule

/-- Collect actual raw expressions by addition and scalar action, without multiplying them. -/
theorem assembly_eq_collected_raw
    (A : StrataRealization C 2 (Fin 1))
    (coeff : ι → Fin 3 → Fin 3 → K) :
    assembly A coeff =
      (∑ p, coeff p 0 0) • A.map raw00Degree0 +
      (∑ p, (coeff p 0 1 + coeff p 1 0)) • A.map raw01Degree1 +
      (∑ p, (coeff p 0 2 + coeff p 2 0)) • A.map raw02Degree2 +
      (∑ p, coeff p 1 1) • A.map raw11Degree2 +
      (∑ p, (coeff p 1 2 + coeff p 2 1)) • A.map raw12Degree3 +
      (∑ p, coeff p 2 2) • A.map raw22Degree4 := by
  simp only [assembly, ← Finset.smul_sum, ← map_sum, sum_rawComponent]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    raw_single_factor_one_symm, raw_single_factor_two_symm,
    ← AdmcyclesHodgeStrataIsomorphisms.raw_ordered_degree3_equal]
  simp only [Finset.sum_add_distrib, Finset.sum_smul, add_smul]
  abel

/-- The complete P² candidate equals this exact raw class, without a scalar projection. -/
theorem plane_candidateClass_eq_raw_regular
    {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass A =
      (x ^ 2 - x * y + y ^ 2) • A.map raw00Degree0 +
      (3 : Coefficient) • A.map raw11Degree2 +
      (3 : Coefficient) • A.map raw02Degree2 := by
  rw [HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass, assembly_eq_collected_raw,
    HodgeDegreeZeroRegularity.Plane.sum_constant,
    HodgeDegreeZeroRegularity.Plane.sum_lambda1,
    HodgeDegreeZeroRegularity.Plane.sum_lambda2,
    HodgeDegreeZeroRegularity.Plane.sum_lambda1Squared,
    HodgeDegreeZeroRegularity.Plane.sum_mixed,
    HodgeDegreeZeroRegularity.Plane.sum_lambda2Squared]
  simp only [zero_smul, add_zero]
  abel

/-- The complete F₁ candidate is four times its exact raw (1,1), degree-two expression. -/
theorem oneBlowup_candidateClass_eq_raw_regular
    {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      (4 : Coefficient) • A.map raw11Degree2 := by
  rw [HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass, assembly_eq_collected_raw,
    HodgeDegreeZeroRegularity.OneBlowup.sum_constant,
    HodgeDegreeZeroRegularity.OneBlowup.sum_lambda1,
    HodgeDegreeZeroRegularity.OneBlowup.sum_lambda2,
    HodgeDegreeZeroRegularity.OneBlowup.sum_lambda1Squared,
    HodgeDegreeZeroRegularity.OneBlowup.sum_mixed,
    HodgeDegreeZeroRegularity.OneBlowup.sum_lambda2Squared]
  simp only [zero_smul, add_zero, zero_add]

/-- The complete two-point blowup candidate retains the signed raw degree-two expressions. -/
theorem twoBlowups_candidateClass_eq_raw_regular
    {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A =
      (-(x ^ 2 - x * y + y ^ 2)) • A.map raw00Degree0 +
      (5 : Coefficient) • A.map raw11Degree2 +
      (-3 : Coefficient) • A.map raw02Degree2 := by
  rw [HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass, assembly_eq_collected_raw,
    HodgeDegreeZeroRegularity.TwoBlowups.sum_constant,
    HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda1,
    HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda2,
    HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda1Squared,
    HodgeDegreeZeroRegularity.TwoBlowups.sum_mixed,
    HodgeDegreeZeroRegularity.TwoBlowups.sum_lambda2Squared]
  simp only [zero_smul, add_zero]
  abel

end

end AxiomaticGW.GKM.HodgeDegreeZeroRawAssembly
