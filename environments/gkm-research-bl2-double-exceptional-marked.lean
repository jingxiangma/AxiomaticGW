-- GKM ordinary comparison, report SHA256 7a34aed723e34370d7916668cff1f08c6c47b1f4f5b3c7a22214b860e3197516
import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalMarked
import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalComparison
import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction

namespace AxiomaticGW.Research.Query_81578f890f54f3a1e7c7

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .blowupTwo := ⟨2, ![2, 0, 0], [⟨.exceptional 0, 0⟩, ⟨.unit, 4⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request (1 / 384 : ℚ) := by
  have hq : request = BlowupTwoDoubleExceptionalMarked.request 0 3 (.unit) false := by decide +kernel
  have hv : BlowupTwoDoubleExceptionalMarked.values 0 3 (.unit) = (1 / 384 : ℚ) := by decide +kernel
  rw [hq, ← hv]
  exact BlowupTwoDoubleExceptionalMarked.checked 0 3 (.unit) false

private abbrev geometricDerivation :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry (X := SurfaceTarget.blowupTwo) (i := 0) (q := request) (hg := rfl) (v := (1 / 384 : ℚ)) (hv := certified)

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C ((1/384) : ℚ))
noncomputable def gkmDenominator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C (1 : ℚ))
noncomputable def gkmFunction : Coefficient := embed gkmNumerator / embed gkmDenominator

/-- The incoming equivariant function is regular in this presentation at zero weights. -/
theorem ordinary_specialization : Specializes gkmFunction (1 / 384 : ℚ) := by
  have hn : atZero gkmNumerator = ((1/384) : ℚ) := by
    norm_num only [gkmNumerator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  have hd : atZero gkmDenominator = (1 : ℚ) := by
    norm_num only [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  refine ⟨gkmNumerator, gkmDenominator, ?_, rfl, ?_⟩
  · exact fun hz ↦ (by decide +kernel : (1 : ℚ) ≠ 0) (hd.symm.trans hz)
  · exact (congrArg₂ (· / ·) hn hd).trans (by decide +kernel)

/-- The exact requested GW computation and the regular GKM specialization agree. -/
theorem comparison : (SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request (1 / 384 : ℚ)) ∧ Specializes gkmFunction (1 / 384 : ℚ) :=
  ⟨certified, ordinary_specialization⟩

/-- The full ordered request and incoming fraction agree with the certified localization row. -/
theorem equivariant_comparison :
    request = GKM.BlowupTwoDoubleExceptionalFewMarkings.requests 155 ∧
      gkmFunction = GKM.BlowupTwoDoubleExceptionalFewMarkings.equivariant 155 := by
  constructor
  · decide +kernel
  · have hv : GKM.BlowupTwoDoubleExceptionalFewMarkings.values 155 = (1 / 384 : ℚ) := by decide +kernel
    have hd : atZero gkmDenominator ≠ 0 := by
      norm_num [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
    rw [GKM.BlowupTwoDoubleExceptionalFewMarkings.equivariant_eq_ordinary, hv, gkmFunction,
      div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [gkmNumerator, gkmDenominator, map_add, map_mul, map_pow, embed_C]

/-- Marking-by-marking comparison to the original F₁ reconstruction, with the full incoming field. -/
theorem exceptional_surface_comparison :
    GKM.BlowupTwoDoubleExceptionalFewMarkings.project? request = (GKM.BlowupTwoDoubleExceptionalFewMarkings.counterpart 155).map (fun c ↦ (GKM.BlowupTwoDoubleExceptionalFewMarkings.sourceRow c).1) ∧
    (∀ c, GKM.BlowupTwoDoubleExceptionalFewMarkings.counterpart 155 = some c →
      SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 (GKM.BlowupTwoDoubleExceptionalFewMarkings.sourceRow c).1 (1 / 384 : ℚ)) ∧
    (GKM.BlowupTwoDoubleExceptionalFewMarkings.counterpart 155 = none → gkmFunction = 0) := by
  rw [equivariant_comparison.1]
  have hv : GKM.BlowupTwoDoubleExceptionalFewMarkings.values 155 = (1 / 384 : ℚ) := by decide +kernel
  exact ⟨(GKM.BlowupTwoDoubleExceptionalFewMarkings.projection 155).1, fun c hc ↦ hv ▸ (GKM.BlowupTwoDoubleExceptionalFewMarkings.matched 155 c hc).2.1,
    fun hc ↦ equivariant_comparison.2.trans (GKM.BlowupTwoDoubleExceptionalFewMarkings.unmatched 155 hc).2⟩

end AxiomaticGW.Research.Query_81578f890f54f3a1e7c7

#print axioms AxiomaticGW.Research.Query_81578f890f54f3a1e7c7.domain
#print axioms AxiomaticGW.Research.Query_81578f890f54f3a1e7c7.certified
#print axioms AxiomaticGW.SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
#print axioms AxiomaticGW.Research.Query_81578f890f54f3a1e7c7.geometric
#print axioms AxiomaticGW.Research.Query_81578f890f54f3a1e7c7.comparison
#print axioms AxiomaticGW.Research.Query_81578f890f54f3a1e7c7.equivariant_comparison
#print axioms AxiomaticGW.Research.Query_81578f890f54f3a1e7c7.exceptional_surface_comparison
