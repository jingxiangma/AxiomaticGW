-- GKM ordinary comparison, report SHA256 ea777037d1eeefd53f5bb90fd9c0c3647e79cba3b3ac0c96c453baedb37c48b5
import AxiomaticGW.Surfaces.GenusOneDescendants
import AxiomaticGW.GKM.EquivariantCoefficients

namespace AxiomaticGW.Research.Query_fd2feb63c70dee285a89

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .hirzebruchOne := ⟨1, ![1, 0], [⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    SurfaceGenusOne.queryValue? request = some (1 / 12 : ℚ) := by
  decide +kernel

private abbrev geometricDerivation :=
  let law := @SurfaceGenusOne.queryValue?_eq_checkedEval (X := SurfaceTarget.hirzebruchOne) (q := request) (hg := rfl)
  show _ from by
    simp only [certified, eq_comm (a := some (1 / 12 : ℚ))] at law
    exact law

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C ((1/12) : ℚ))
noncomputable def gkmDenominator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C (1 : ℚ))
noncomputable def gkmFunction : Coefficient := embed gkmNumerator / embed gkmDenominator

/-- The incoming equivariant function is regular in this presentation at zero weights. -/
theorem ordinary_specialization : Specializes gkmFunction (1 / 12 : ℚ) := by
  have hn : atZero gkmNumerator = ((1/12) : ℚ) := by
    norm_num only [gkmNumerator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  have hd : atZero gkmDenominator = (1 : ℚ) := by
    norm_num only [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  refine ⟨gkmNumerator, gkmDenominator, ?_, rfl, ?_⟩
  · exact fun hz ↦ (by decide +kernel : (1 : ℚ) ≠ 0) (hd.symm.trans hz)
  · exact (congrArg₂ (· / ·) hn hd).trans (by decide +kernel)

/-- The exact requested GW computation and the regular GKM specialization agree. -/
theorem comparison : (SurfaceGenusOne.queryValue? request = some (1 / 12 : ℚ)) ∧ Specializes gkmFunction (1 / 12 : ℚ) :=
  ⟨certified, ordinary_specialization⟩

end AxiomaticGW.Research.Query_fd2feb63c70dee285a89

#print axioms AxiomaticGW.Research.Query_fd2feb63c70dee285a89.domain
#print axioms AxiomaticGW.Research.Query_fd2feb63c70dee285a89.certified
#print axioms AxiomaticGW.SurfaceGenusOne.queryValue?_eq_checkedEval
#print axioms AxiomaticGW.Research.Query_fd2feb63c70dee285a89.geometric
#print axioms AxiomaticGW.Research.Query_fd2feb63c70dee285a89.comparison
