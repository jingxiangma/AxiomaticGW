module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRegularity

@[expose] public section

namespace AxiomaticGWTest.HodgeDegreeZeroRegularity

open AxiomaticGW.GKM HodgeDegreeZeroRegularity

/-- An explicit regular lift witnesses the complete actual fixed-point sum. -/
theorem plane_regular_specialization :
    ∃ P : RegularHodgePolynomial,
      MvPolynomial.map EquivariantCoefficients.embed P = Plane.completePolynomial ∧
      MvPolynomial.map EquivariantCoefficients.atZero P =
        3 * MvPolynomial.X 0 ^ 2 + (3) * MvPolynomial.X 1 :=
  ⟨Plane.regularLift, Plane.map_embed_regularLift, Plane.map_atZero_regularLift⟩

/-- An explicit regular lift witnesses the complete actual fixed-point sum. -/
theorem oneBlowup_regular_specialization :
    ∃ P : RegularHodgePolynomial,
      MvPolynomial.map EquivariantCoefficients.embed P = OneBlowup.completePolynomial ∧
      MvPolynomial.map EquivariantCoefficients.atZero P =
        4 * MvPolynomial.X 0 ^ 2 + (0) * MvPolynomial.X 1 :=
  ⟨OneBlowup.regularLift, OneBlowup.map_embed_regularLift, OneBlowup.map_atZero_regularLift⟩

/-- An explicit regular lift witnesses the complete actual fixed-point sum. -/
theorem twoBlowups_regular_specialization :
    ∃ P : RegularHodgePolynomial,
      MvPolynomial.map EquivariantCoefficients.embed P = TwoBlowups.completePolynomial ∧
      MvPolynomial.map EquivariantCoefficients.atZero P =
        5 * MvPolynomial.X 0 ^ 2 + (-3) * MvPolynomial.X 1 :=
  ⟨TwoBlowups.regularLift, TwoBlowups.map_embed_regularLift, TwoBlowups.map_atZero_regularLift⟩

end AxiomaticGWTest.HodgeDegreeZeroRegularity
