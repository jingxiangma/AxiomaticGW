/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeGeometricVertex
public import AxiomaticGW.GKM.Fixtures.StrictLineDoubleCoverChain

/-! # The two-character contribution of a marked genus-two fixed graph on the doubled strict line

The central vertex is integrated on the three-marked genus-two source curve. The two rational
ends retain their original Euler and insertion conventions. Their common exchange contributes
a factor of one half.
-/

@[expose] public section
namespace AxiomaticGW.GKM.StrictLineDoubleCoverChain
open GenusTwoLocalizationClass GenusTwoHodgeGeometricVertex GenusTwoHodgePicardMoments
open GenusTwoHodgeNormalization EquivariantCoefficients PsiBoundaryExpansion

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- Under the curve geometry inputs, integration with the two actual flag weights gives the
exact rational function of this single τ₃(E₂) fixed locus in class (0,0,2). -/
theorem geometric_locus (H : D.Natural) (U : ForgetfulPushforward C I)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (G : GluingForgetfulCompatibility F N)
    {A : ∀ g S, [Fintype S] → StrataRealization C g S}
    (B : PicardRealization D F N A) (E : Normalization D N) (ell : EllipticPsi P F N A)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (dvv : PointTarget.DVVRecursion P I) :
    withCenter (integrate I _ (integrand D P [3] (-x) y (fun _ : Fin 2 ↦ -x))) =
      rationalExpression x y := by
  rw [integrated_vertex H U F N P K hK T Q G B E ell vol base square dvv]
  change withCenter (ExceptionalDoubleCoverChain.center [3] (-x) y) = _
  rw [← bivalent]
  exact locus_value

end AxiomaticGW.GKM.StrictLineDoubleCoverChain
