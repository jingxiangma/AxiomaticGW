-- GKM ordinary comparison, report SHA256 a48c40b5407ee9d2ba7fe7f3483ed76b31fce7ae7de1db9b291905a38daf2794
import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleLineReplay
import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoSingletons
import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction

namespace AxiomaticGW.Research.Query_96cc95498663b75c5e49

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .blowupTwo := ⟨2, ![0, 0, 2], [⟨.exceptional 1, 3⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request (-3 / 320 : ℚ) := by
  have hq : request = GKM.BlowupTwoDoubleLineReplay.requests 3 := by decide +kernel
  have hv : GKM.BlowupTwoDoubleLineReplay.values 3 = (-3 / 320 : ℚ) := by decide +kernel
  rw [hq, ← hv]
  exact GKM.BlowupTwoDoubleLineReplay.accepted 3

private abbrev geometricDerivation :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry (X := SurfaceTarget.blowupTwo) (i := 0) (q := request) (hg := rfl) (v := (-3 / 320 : ℚ)) (hv := certified)

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C ((-3/320) : ℚ))
noncomputable def gkmDenominator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C (1 : ℚ))
noncomputable def gkmFunction : Coefficient := embed gkmNumerator / embed gkmDenominator

/-- The incoming equivariant function is regular in this presentation at zero weights. -/
theorem ordinary_specialization : Specializes gkmFunction (-3 / 320 : ℚ) := by
  have hn : atZero gkmNumerator = ((-3/320) : ℚ) := by
    norm_num only [gkmNumerator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  have hd : atZero gkmDenominator = (1 : ℚ) := by
    norm_num only [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  refine ⟨gkmNumerator, gkmDenominator, ?_, rfl, ?_⟩
  · exact fun hz ↦ (by decide +kernel : (1 : ℚ) ≠ 0) (hd.symm.trans hz)
  · exact (congrArg₂ (· / ·) hn hd).trans (by decide +kernel)

/-- The exact requested GW computation and the regular GKM specialization agree. -/
theorem comparison : (SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request (-3 / 320 : ℚ)) ∧ Specializes gkmFunction (-3 / 320 : ℚ) :=
  ⟨certified, ordinary_specialization⟩

/-- The full ordered request and incoming fraction agree with the certified localization row. -/
theorem equivariant_comparison :
    request = GKM.BlowupTwoPositivePlaneEnergyTwoSingletons.requests 3 ∧
      gkmFunction = GKM.BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant 3 := by
  constructor
  · decide +kernel
  · have hv : GKM.BlowupTwoPositivePlaneEnergyTwoSingletons.values 3 = (-3 / 320 : ℚ) := by decide +kernel
    have hd : atZero gkmDenominator ≠ 0 := by
      norm_num [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
    rw [GKM.BlowupTwoPositivePlaneEnergyTwoSingletons.equivariant_eq_ordinary, hv, gkmFunction,
      div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [gkmNumerator, gkmDenominator, map_add, map_mul, map_pow, embed_C]

end AxiomaticGW.Research.Query_96cc95498663b75c5e49

#print axioms AxiomaticGW.Research.Query_96cc95498663b75c5e49.domain
#print axioms AxiomaticGW.Research.Query_96cc95498663b75c5e49.certified
#print axioms AxiomaticGW.SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
#print axioms AxiomaticGW.Research.Query_96cc95498663b75c5e49.geometric
#print axioms AxiomaticGW.Research.Query_96cc95498663b75c5e49.comparison
#print axioms AxiomaticGW.Research.Query_96cc95498663b75c5e49.equivariant_comparison
