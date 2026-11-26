module

public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataIsomorphisms

@[expose] public section

namespace AxiomaticGWTest.AdmcyclesHodgeStrataIsomorphisms

open AxiomaticGW
open AxiomaticGW.AdmcyclesHodgeStrataCandidates
open AxiomaticGW.AdmcyclesHodgeStrataIsomorphisms

/-- Public consumers get equality of the exact two decoded raw expressions. -/
theorem exact_raw_inputs_equal : raw_1_2_degree3 = raw_2_1_degree3 :=
  raw_ordered_degree3_equal

/-- The common expression remains in degree three of the free strata module. -/
theorem common_expression_degree :
    RelationCertificate.interpret representatives collectedCoordinates ∈
      StrataModule.degree 3 := by
  rw [← raw_1_2_eq_collected]
  exact raw_1_2_degree3_mem_degree

/-- The checked equality persists after any given rational linear realization. -/
theorem equality_under_linear_map
    (M : Type) [AddCommGroup M] [Module ℚ M]
    (f : StrataModule 2 (Fin 1) →ₗ[ℚ] M) :
    f raw_1_2_degree3 = f raw_2_1_degree3 :=
  congrArg f raw_ordered_degree3_equal

end AxiomaticGWTest.AdmcyclesHodgeStrataIsomorphisms
