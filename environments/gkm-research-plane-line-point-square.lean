-- GKM ordinary comparison, report SHA256 1a94832bf151485490eb3f71773526a92f46b248ccd25879e6bd993b21b59f53
import AxiomaticGW.Surfaces.DimensionVanishing
import AxiomaticGW.GKM.Fixtures.PlaneLineOneMarkedPoint

namespace AxiomaticGW.Research.Query_df5e71bb8b275d700e3b

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .plane := ⟨0, ![1], [⟨.point, 2⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    request.dimensionVanishing? = some (0 / 1 : ℚ) := by
  decide +kernel

private abbrev geometricDerivation :=
  @SurfaceQuery.dimensionVanishing?_sound (X := SurfaceTarget.plane) (q := request) (hg := domain) (v := (0 / 1 : ℚ)) (hv := certified)

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C (2 : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C (-1 : ℚ))*(MvPolynomial.X 0)
noncomputable def gkmDenominator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C (1 : ℚ))
noncomputable def gkmFunction : Coefficient := embed gkmNumerator / embed gkmDenominator

/-- The incoming equivariant function is regular in this presentation at zero weights. -/
theorem ordinary_specialization : Specializes gkmFunction (0 / 1 : ℚ) := by
  have hn : atZero gkmNumerator = (0 : ℚ) := by
    norm_num only [gkmNumerator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  have hd : atZero gkmDenominator = (1 : ℚ) := by
    norm_num only [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
  refine ⟨gkmNumerator, gkmDenominator, ?_, rfl, ?_⟩
  · exact fun hz ↦ (by decide +kernel : (1 : ℚ) ≠ 0) (hd.symm.trans hz)
  · exact (congrArg₂ (· / ·) hn hd).trans (by decide +kernel)

/-- The exact requested GW computation and the regular GKM specialization agree. -/
theorem comparison : (request.dimensionVanishing? = some (0 / 1 : ℚ)) ∧ Specializes gkmFunction (0 / 1 : ℚ) :=
  ⟨certified, ordinary_specialization⟩

/-- The supplied two-character fraction equals the marked plane line's two-flag sum. -/
theorem equivariant_comparison :
    request = GKM.PlaneLineOneMarkedPoint.requests 2 ∧ gkmFunction = GKM.PlaneLineOneMarkedPoint.equivariant 2 := by
  constructor
  · decide +kernel
  · have hd : atZero gkmDenominator ≠ 0 := by
      norm_num [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
    rw [GKM.PlaneLineOneMarkedPoint.equivariant_eq_polynomial, gkmFunction,
      div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [gkmNumerator, gkmDenominator, GKM.PlaneLineOneMarkedPoint.polynomial, map_add, map_mul, map_sub,
      map_pow, embed_C, embed_X_zero, embed_X_one]
    all_goals ring

/-- The complete field value equals the sum of the six original oriented fixed-locus factors. -/
theorem fixed_locus_comparison : gkmFunction =
    ∑ e : Fin 3, (GKM.PlaneLineOneMarkedPoint.flag 2 e false + GKM.PlaneLineOneMarkedPoint.flag 2 e true) :=
  equivariant_comparison.2.trans (GKM.PlaneLineOneMarkedPoint.sum_flags 2).symm

/-- The supplied regular polynomial has the equivariant degree of this descendant. -/
theorem equivariant_grading : ∃ p : GKM.EquivariantCoefficients.Polynomial,
    p.IsHomogeneous 1 ∧ gkmFunction = embed p :=
  ⟨GKM.PlaneLineOneMarkedPoint.polynomial 2, GKM.PlaneLineOneMarkedPoint.polynomial_homogeneous 1,
    equivariant_comparison.2.trans (GKM.PlaneLineOneMarkedPoint.equivariant_eq_polynomial 2)⟩

end AxiomaticGW.Research.Query_df5e71bb8b275d700e3b

#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.domain
#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.certified
#print axioms AxiomaticGW.SurfaceQuery.dimensionVanishing?_sound
#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.geometric
#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.comparison
#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.fixed_locus_comparison
#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.equivariant_grading
#print axioms AxiomaticGW.Research.Query_df5e71bb8b275d700e3b.equivariant_comparison
