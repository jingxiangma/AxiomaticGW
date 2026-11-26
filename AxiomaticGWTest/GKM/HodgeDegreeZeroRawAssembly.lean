module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRawAssembly

@[expose] public section

set_option autoImplicit false

namespace AxiomaticGWTest.HodgeDegreeZeroRawAssembly

open AxiomaticGW AxiomaticGW.GKM
open AdmcyclesHodgeStrataCandidates EquivariantCoefficients HodgeDegreeZeroRawAssembly

noncomputable section

attribute [local instance] strataRealizationModule

/-- A consumer obtains the complete class using A alone, with no D or hfund input. -/
theorem plane_full_class {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass A -
      (x ^ 2 - x * y + y ^ 2) • A.map raw00Degree0 =
      (3 : Coefficient) • A.map raw11Degree2 +
      (3 : Coefficient) • A.map raw02Degree2 := by
  rw [plane_candidateClass_eq_raw_regular]
  abel

/-- Both blowup candidates keep their actual raw degree-two sums, including the minus sign. -/
theorem blowup_full_class_comparison {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A +
      (x ^ 2 - x * y + y ^ 2) • A.map raw00Degree0 -
      HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      A.map raw11Degree2 - (3 : Coefficient) • A.map raw02Degree2 := by
  rw [twoBlowups_candidateClass_eq_raw_regular, oneBlowup_candidateClass_eq_raw_regular]
  rw [show (5 : Coefficient) = (4 : Coefficient) + 1 by norm_num only, add_smul, one_smul]
  simp only [neg_smul]
  abel

/-- The original degree-four packet expression is retained by the raw component reduction. -/
theorem degree_four_input_retained :
    (∑ d : Fin 5, AdmcyclesHodgeStrataNormalization.rawComponent 2 2 d) =
      raw22Degree4 := by
  simpa only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    sum_rawComponent 2 2

end

end AxiomaticGWTest.HodgeDegreeZeroRawAssembly
