module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeTwoRawRelation

@[expose] public section

set_option autoImplicit false

namespace AxiomaticGWTest.HodgeDegreeTwoRawRelation

open AxiomaticGW AxiomaticGW.GKM
open AdmcyclesHodgeStrataCandidates HodgeDegreeTwoRawRelation EquivariantCoefficients

noncomputable section

/-- Any rational linear map preserves the equality of the original complete raw sums. -/
theorem exact_relation_under_linear_map
    (M : Type) [AddCommGroup M] [Module ℚ M]
    (f : StrataModule 2 (Fin 1) →ₗ[ℚ] M) :
    f raw_1_1_degree2 = (2 : ℚ) • f raw_0_2_degree2 := by
  rw [raw_degree_two_equal, map_smul]

/-- The original degree-two expression is retained, rather than replaced by zero. -/
theorem common_expression_degree :
    RelationCertificate.interpret representatives collectedCoordinates ∈
      StrataModule.degree 2 := by
  rw [← raw_0_2_eq_collected]
  exact raw_0_2_degree2_mem_degree

attribute [local instance] strataRealizationModule

/-- The complete fixed-point sum is available without D, hfund, or a product premise. -/
theorem oneBlowup_complete_class {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      (8 : Coefficient) • A.map raw_0_2_degree2 :=
  oneBlowup_candidateClass_eq_raw_degree_two A

/-- The two surfaces differ by the actual unit term and one copy of the degree-two class. -/
theorem blowup_complete_class_difference {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A +
      (x ^ 2 - x * y + y ^ 2) • A.map raw_0_0_degree0 -
      HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      -A.map raw_0_2_degree2 := by
  rw [twoBlowups_candidateClass_eq_raw_degree_two, oneBlowup_candidateClass_eq_raw_degree_two]
  rw [show (8 : Coefficient) = (7 : Coefficient) + 1 by norm_num only,
    add_smul (7 : Coefficient) 1 (A.map raw_0_2_degree2), one_smul]
  simp only [neg_smul]
  abel

end

end AxiomaticGWTest.HodgeDegreeTwoRawRelation
