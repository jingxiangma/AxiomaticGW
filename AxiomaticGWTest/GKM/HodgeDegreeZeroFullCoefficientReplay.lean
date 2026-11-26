module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroFullCoefficientReplay

@[expose] public section

namespace AxiomaticGWTest.HodgeDegreeZeroFullCoefficientReplay

open AxiomaticGW AxiomaticGW.GKM
open EquivariantCoefficients
open AdmcyclesHodgeStrataNormalization

variable {C : StableCurveCohomology Coefficient}

attribute [local instance] strataRealizationModule

/-- Every positive and zero-degree coefficient has a checked denominator. -/
theorem plane_all_denominators (p : Fin 3) (a b : Fin 3) :
    embed (HodgeDegreeZeroFullCoefficientReplay.Plane.denominators p a b) ≠ 0 :=
  HodgeDegreeZeroFullCoefficientReplay.Plane.denominator_ne_zero p a b

/-- All coefficients occur before scalar projection, under the original realization inputs. -/
theorem plane_complete_normalization (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :
    D.scalar 2 (Fin 1) stable (HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass A) =
      (FixedPointAlgebra.algebra SurfaceReplay.Plane.accepted.eulerUnits).correlator
        2 (Fin 1) (fun _ ↦ 1) :=
  HodgeDegreeZeroFullCoefficientReplay.Plane.scalar_candidateClass_eq_tft D A hfund

/-- Every positive and zero-degree coefficient has a checked denominator. -/
theorem oneBlowup_all_denominators (p : Fin 4) (a b : Fin 3) :
    embed (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.denominators p a b) ≠ 0 :=
  HodgeDegreeZeroFullCoefficientReplay.OneBlowup.denominator_ne_zero p a b

/-- All coefficients occur before scalar projection, under the original realization inputs. -/
theorem oneBlowup_complete_normalization (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :
    D.scalar 2 (Fin 1) stable (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A) =
      (FixedPointAlgebra.algebra SurfaceReplay.OneBlowup.accepted.eulerUnits).correlator
        2 (Fin 1) (fun _ ↦ 1) :=
  HodgeDegreeZeroFullCoefficientReplay.OneBlowup.scalar_candidateClass_eq_tft D A hfund

/-- Every positive and zero-degree coefficient has a checked denominator. -/
theorem twoBlowups_all_denominators (p : Fin 5) (a b : Fin 3) :
    embed (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.denominators p a b) ≠ 0 :=
  HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.denominator_ne_zero p a b

/-- All coefficients occur before scalar projection, under the original realization inputs. -/
theorem twoBlowups_complete_normalization (D : ConnectedDegreeZero C)
    (A : StrataRealization C 2 (Fin 1))
    (hfund : A.map (StrataModule.basis
      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :
    D.scalar 2 (Fin 1) stable (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A) =
      (FixedPointAlgebra.algebra SurfaceReplay.TwoBlowups.accepted.eulerUnits).correlator
        2 (Fin 1) (fun _ ↦ 1) :=
  HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.scalar_candidateClass_eq_tft D A hfund

end AxiomaticGWTest.HodgeDegreeZeroFullCoefficientReplay
