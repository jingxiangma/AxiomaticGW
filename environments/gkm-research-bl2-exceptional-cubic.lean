-- GKM ordinary comparison, report SHA256 f6abaecbd19a065f72b2dcf8e9e1330d48ff8916a482a2af57bcb078ce15dd29
import AxiomaticGW.Surfaces.DimensionVanishing
import AxiomaticGW.GKM.Fixtures.ExceptionalCubicGeometricLoci

namespace AxiomaticGW.Research.Query_46337d2545e9696470ac

/-- Requested genus, effective class and ordered descendants. -/
def request : SurfaceQuery .blowupTwo := ⟨2, ![1, 0, 0], [⟨.exceptional 0, 3⟩]⟩

/-- The request is in the geometric query domain. -/
theorem domain : request.GeometricDomain := by decide +kernel

/-- Exact answer from the specified surface query evaluator. -/
theorem certified :
    request.dimensionVanishing? = some (0 / 1 : ℚ) := by
  decide +kernel

private abbrev geometricDerivation :=
  @SurfaceQuery.dimensionVanishing?_sound (X := SurfaceTarget.blowupTwo) (q := request) (hg := domain) (v := (0 / 1 : ℚ)) (hv := certified)

/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/
theorem geometric : type_of% geometricDerivation := geometricDerivation

open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  (MvPolynomial.C ((1/240) : ℚ))*(MvPolynomial.X 1)
    + (MvPolynomial.C ((1/240) : ℚ))*(MvPolynomial.X 0)
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

/-- The original full request and both equivariant characters agree with the cubic calculation. -/
theorem equivariant_comparison :
    request = GKM.ExceptionalGenusTwoCubicReplay.requests .first ∧ gkmFunction = GKM.ExceptionalGenusTwoCubicReplay.equivariant .first := by
  constructor
  · decide +kernel
  · have hd : atZero gkmDenominator ≠ 0 := by norm_num [gkmDenominator, atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply]
    rw [gkmFunction, div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [GKM.ExceptionalGenusTwoCubicReplay.equivariant, gkmNumerator, gkmDenominator, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one]
    all_goals ring

/-- The incoming rational function equals the sum over the three genus distributions
and two marked endpoints of the exceptional edge. -/
theorem fixed_locus_comparison : gkmFunction = ∑ g : Fin 3, ∑ m : Fin 2, GKM.ExceptionalGenusTwoCubicReplay.locus .first g m :=
  equivariant_comparison.2.trans (GKM.ExceptionalGenusTwoCubicReplay.sum_loci .first).symm

private abbrev integratedLocusDerivation :=
  let law := @GKM.ExceptionalCubicGeometricLoci.geometric_sum (c := .first)
  show _ from by
    simp only [← equivariant_comparison.2] at law
    exact law

/-- Under the curve and Hodge class identities, integrating the stable vertices and summing
the six signed primitive exceptional loci gives this exact incoming character function. -/
theorem integrated_locus_comparison : type_of% integratedLocusDerivation := integratedLocusDerivation

end AxiomaticGW.Research.Query_46337d2545e9696470ac

#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.domain
#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.certified
#print axioms AxiomaticGW.SurfaceQuery.dimensionVanishing?_sound
#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.geometric
#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.comparison
#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.fixed_locus_comparison
#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.integrated_locus_comparison
#print axioms AxiomaticGW.Research.Query_46337d2545e9696470ac.equivariant_comparison
