module

public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates

@[expose] public section

namespace AxiomaticGWTest.AdmcyclesHodgeStrataCandidates

open AxiomaticGW
open AxiomaticGW.AdmcyclesHodgeStrataCandidates

/-- The highest nonempty component uses all node/kappa/psi degree accounting. -/
theorem raw_top_degree : raw_2_2_degree4 ∈ StrataModule.degree 4 :=
  raw_2_2_degree4_mem_degree

/-- Both ordered mixed representatives are retained independently. -/
theorem ordered_mixed_degrees :
    raw_1_2_degree3 ∈ StrataModule.degree 3 ∧
      raw_2_1_degree3 ∈ StrataModule.degree 3 :=
  ⟨raw_1_2_degree3_mem_degree, raw_2_1_degree3_mem_degree⟩

/-- An explicit empty degree component is the zero formal expression. -/
theorem empty_component_zero : raw_0_0_degree4 = 0 := by
  rw [raw_0_0_degree4, RelationCertificate.interpret_apply]
  exact Fin.sum_univ_zero _

/-- The empty component remains in its recorded degree subspace. -/
theorem empty_component_degree : raw_0_0_degree4 ∈ StrataModule.degree 4 :=
  raw_0_0_degree4_mem_degree

/-- The degree-zero input is a stable genus-two marked vertex. -/
theorem degree_zero_column_valid : rawIncidence0Candidate.Valid 2 := rawIncidence0Valid

end AxiomaticGWTest.AdmcyclesHodgeStrataCandidates
