module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientFormula

@[expose] public section

namespace AxiomaticGWTest.HodgeDegreeZeroCoefficientFormula

open AxiomaticGW.GKM HodgeDegreeZeroCoefficientFormula

/-- Each source-ordered coefficient is checked, including the asymmetric pairs. -/
theorem plane_all_coefficients (p : Fin 3) (a b : Fin 3) :
    HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p a b =
      orderedChernCoefficient (Plane.tangentWeight p 0) (Plane.tangentWeight p 1) a b :=
  Plane.coefficients_eq_orderedChern p a b

/-- Formal polynomial equality is about the complete actual incoming coefficient tensor. -/
theorem plane_full_polynomial (p : Fin 3) :
    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.Plane.coefficients p) =
      MvPolynomial.C ((Plane.tangentWeight p 0 * Plane.tangentWeight p 1)⁻¹) *
        chernPolynomial (Plane.tangentWeight p 0) *
          chernPolynomial (Plane.tangentWeight p 1) :=
  Plane.hodgePolynomial_eq p

/-- Each source-ordered coefficient is checked, including the asymmetric pairs. -/
theorem oneBlowup_all_coefficients (p : Fin 4) (a b : Fin 3) :
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p a b =
      orderedChernCoefficient (OneBlowup.tangentWeight p 0) (OneBlowup.tangentWeight p 1) a b :=
  OneBlowup.coefficients_eq_orderedChern p a b

/-- Formal polynomial equality is about the complete actual incoming coefficient tensor. -/
theorem oneBlowup_full_polynomial (p : Fin 4) :
    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.OneBlowup.coefficients p) =
      MvPolynomial.C ((OneBlowup.tangentWeight p 0 * OneBlowup.tangentWeight p 1)⁻¹) *
        chernPolynomial (OneBlowup.tangentWeight p 0) *
          chernPolynomial (OneBlowup.tangentWeight p 1) :=
  OneBlowup.hodgePolynomial_eq p

/-- Each source-ordered coefficient is checked, including the asymmetric pairs. -/
theorem twoBlowups_all_coefficients (p : Fin 5) (a b : Fin 3) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p a b =
      orderedChernCoefficient (TwoBlowups.tangentWeight p 0) (TwoBlowups.tangentWeight p 1) a b :=
  TwoBlowups.coefficients_eq_orderedChern p a b

/-- Formal polynomial equality is about the complete actual incoming coefficient tensor. -/
theorem twoBlowups_full_polynomial (p : Fin 5) :
    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.coefficients p) =
      MvPolynomial.C ((TwoBlowups.tangentWeight p 0 * TwoBlowups.tangentWeight p 1)⁻¹) *
        chernPolynomial (TwoBlowups.tangentWeight p 0) *
          chernPolynomial (TwoBlowups.tangentWeight p 1) :=
  TwoBlowups.hodgePolynomial_eq p

end AxiomaticGWTest.HodgeDegreeZeroCoefficientFormula
