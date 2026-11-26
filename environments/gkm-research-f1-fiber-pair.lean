-- GKM ordinary comparison, report SHA256 c8d06640ee690ec6f86cc370964c2c3cfba863432cfca16bb5b3009c3656e092
import AxiomaticGW.GKM.Fixtures.F1FiberPairsReplay
import AxiomaticGW.GKM.Fixtures.F1FiberPairs
import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction

namespace AxiomaticGW.Research.Query_76798e3977363f6c53ad

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .hirzebruchOne := ⟨2, ![0, 1], [⟨.unit, 3⟩, ⟨.exceptional 0, 1⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request (-113 / 2880 : ℚ) := by
  have hq : request = GKM.F1FiberPairs.requests 14 := by decide +kernel
  have hv : GKM.F1FiberPairs.values 14 = (-113 / 2880 : ℚ) := by decide +kernel
  rw [hq, ← hv]
  exact GKM.F1FiberPairs.accepted 14

private abbrev geometricDerivation :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry (X := SurfaceTarget.hirzebruchOne) (i := 0) (q := request) (hg := rfl) (v := (-113 / 2880 : ℚ)) (hv := certified)

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C ((-113/2880) : ℚ))
noncomputable def gkmDenominator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C (1 : ℚ))
noncomputable def gkmFunction : Coefficient := embed gkmNumerator / embed gkmDenominator

/-- The incoming equivariant function is regular in this presentation at zero weights. -/
theorem ordinary_specialization : Specializes gkmFunction (-113 / 2880 : ℚ) := by
  have hn : atZero gkmNumerator = ((-113/2880) : ℚ) := by
    norm_num only [gkmNumerator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  have hd : atZero gkmDenominator = (1 : ℚ) := by
    norm_num only [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  refine ⟨gkmNumerator, gkmDenominator, ?_, rfl, ?_⟩
  · exact fun hz ↦ (by decide +kernel : (1 : ℚ) ≠ 0) (hd.symm.trans hz)
  · exact (congrArg₂ (· / ·) hn hd).trans (by decide +kernel)

/-- The exact requested GW computation and the regular GKM specialization agree. -/
theorem comparison : (SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request (-113 / 2880 : ℚ)) ∧ Specializes gkmFunction (-113 / 2880 : ℚ) :=
  ⟨certified, ordinary_specialization⟩

/-- The full ordered request and incoming fraction agree with the certified localization row. -/
theorem equivariant_comparison :
    request = GKM.F1FiberPairs.requests 14 ∧
      gkmFunction = GKM.F1FiberPairs.equivariant 14 := by
  constructor
  · decide +kernel
  · have hv : GKM.F1FiberPairs.values 14 = (-113 / 2880 : ℚ) := by decide +kernel
    have hd : atZero gkmDenominator ≠ 0 := by
      norm_num [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
    rw [GKM.F1FiberPairs.equivariant_eq_ordinary, hv, gkmFunction,
      div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [gkmNumerator, gkmDenominator, map_add, map_mul, map_pow, embed_C]

end AxiomaticGW.Research.Query_76798e3977363f6c53ad

#print axioms AxiomaticGW.Research.Query_76798e3977363f6c53ad.domain
#print axioms AxiomaticGW.Research.Query_76798e3977363f6c53ad.certified
#print axioms AxiomaticGW.SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
#print axioms AxiomaticGW.Research.Query_76798e3977363f6c53ad.geometric
#print axioms AxiomaticGW.Research.Query_76798e3977363f6c53ad.comparison
#print axioms AxiomaticGW.Research.Query_76798e3977363f6c53ad.equivariant_comparison
