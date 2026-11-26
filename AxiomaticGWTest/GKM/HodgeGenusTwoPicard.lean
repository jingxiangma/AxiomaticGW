module

public import AxiomaticGW.GKM.Fixtures.HodgeOrdinaryBoundarySquare

@[expose] public section
namespace AxiomaticGWTest.GKM.HodgeGenusTwoPicard
open AxiomaticGW AxiomaticGW.GKM HodgeGenusTwoPicard AdmcyclesHodgeStrataCandidates

/-- The marked loop contributes one twentieth in the degree-one packet after descent,
and the single marked separating boundary contributes one fifth. -/
theorem projected_weights {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ev : StrataModule 2 (Fin 1) →ₗ[ℚ] V)
    (hrow : ev (RelationCertificate.interpret columns row) = 0) :
    ev raw01Degree1 = (1 / 20 : ℚ) • ev (StrataModule.basis rawGraph3) +
      (1 / 5 : ℚ) • ev (StrataModule.basis rawGraph4) := by
  rw [map_degree_one ev hrow, boundary, map_add, map_smul, map_smul, smul_add,
    smul_smul, smul_smul]
  norm_num

/-- Dropping the source row would falsely claim equality in the free strata module.
Summing its raw coefficients detects the difference. -/
theorem free_packet_is_distinct : (10 : ℚ) • raw01Degree1 ≠ boundary := by
  intro h
  have he := congrArg
    (Finsupp.linearCombination ℚ (fun _ : TautologicalStratum 2 (Fin 1) ↦ (1 : ℚ))) raw_residual
  rw [h, sub_self, map_zero, map_smul] at he
  simp only [RelationCertificate.interpret_apply, map_sum, map_smul, StrataModule.basis,
    Finsupp.linearCombination_single, smul_eq_mul, mul_one] at he
  exact (by decide +kernel : ¬(0 : ℚ) = (-1 / 36) * ∑ j, row j) he

end AxiomaticGWTest.GKM.HodgeGenusTwoPicard
