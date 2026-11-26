module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientReplay

@[expose] public section

namespace AxiomaticGWTest.HodgeDegreeZeroCoefficientReplay

open AxiomaticGW.GKM
open EquivariantCoefficients

/-- Every actual incoming c00 entry supplies the normalization consumer. -/
theorem plane_all_c00 (p : Fin 3) :
    HodgeDegreeZeroCoefficientReplay.Plane.coefficient00 p =
      (SurfaceReplay.Plane.accepted.eulerUnits p : Coefficient) :=
  HodgeDegreeZeroCoefficientReplay.Plane.coefficient00_eq_eulerUnits p

/-- Every actual incoming c00 entry supplies the normalization consumer. -/
theorem oneBlowup_all_c00 (p : Fin 4) :
    HodgeDegreeZeroCoefficientReplay.OneBlowup.coefficient00 p =
      (SurfaceReplay.OneBlowup.accepted.eulerUnits p : Coefficient) :=
  HodgeDegreeZeroCoefficientReplay.OneBlowup.coefficient00_eq_eulerUnits p

/-- Every actual incoming c00 entry supplies the normalization consumer. -/
theorem twoBlowups_all_c00 (p : Fin 5) :
    HodgeDegreeZeroCoefficientReplay.TwoBlowups.coefficient00 p =
      (SurfaceReplay.TwoBlowups.accepted.eulerUnits p : Coefficient) :=
  HodgeDegreeZeroCoefficientReplay.TwoBlowups.coefficient00_eq_eulerUnits p

end AxiomaticGWTest.HodgeDegreeZeroCoefficientReplay
