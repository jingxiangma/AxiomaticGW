import AxiomaticGW.Surfaces.PlaneGenusTwoBenchmarks

namespace AxiomaticGW.Research.Query_7fbcf0b088d4d3b0d57f

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .plane := ⟨2, ![4], [⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    BelorousskiPandharipande.planeCheckCanonicalClaim 4 PlaneGenusTwoScalarTable.values request (27 / 1 : ℚ) = true := by
  exact SurfaceGenusTwo.planeCanonicalBenchmark?_sound _ _ (by decide +kernel)

private abbrev geometricDerivation :=
  @BelorousskiPandharipande.planeCheckCanonicalClaim_checkedEval_from_geometry (bound := 4) (values := PlaneGenusTwoScalarTable.values) (query := request) (claimed := (27 / 1 : ℚ)) (hcheck := certified)

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

end AxiomaticGW.Research.Query_7fbcf0b088d4d3b0d57f

#print axioms AxiomaticGW.Research.Query_7fbcf0b088d4d3b0d57f.domain
#print axioms AxiomaticGW.Research.Query_7fbcf0b088d4d3b0d57f.certified
#print axioms AxiomaticGW.BelorousskiPandharipande.planeCheckCanonicalClaim_checkedEval_from_geometry
#print axioms AxiomaticGW.Research.Query_7fbcf0b088d4d3b0d57f.geometric
