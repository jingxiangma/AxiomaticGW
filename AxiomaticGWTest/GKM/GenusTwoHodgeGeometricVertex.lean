import AxiomaticGW.GKM.Fixtures.StrictLineGraphVertices
import AxiomaticGW.GKM.Fixtures.ExceptionalDoubleCoverChain

/-! # Integrated genus-two localization with all Hodge moments supplied by geometry -/

namespace AxiomaticGWTest.GKM.GenusTwoHodgeGeometricVertex
open AxiomaticGW AxiomaticGW.GKM
open GenusTwoLocalizationClass PsiBoundaryExpansion GenusTwoHodgeNormalization
open GenusTwoHodgePicardMoments GenusTwoHodgeGeometricVertex

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- The native bivalent genus-two component at nonzero tangent and flag weights. -/
theorem bivalent (H : D.Natural) (U : ForgetfulPushforward C I)
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
    integrate I _ (integrand D P [3] (3 : ℚ) 2 (fun _ : Fin 2 ↦ 3)) = -199 / 466560 := by
  rw [integrated_vertex H U F N P K hK T Q G B E ell vol base square dvv]
  change ExceptionalDoubleCoverChain.center [3] 3 2 = _
  rw [(ExceptionalDoubleCoverChain.center_eq (3 : ℚ) 2 (by decide) (by decide)).1]
  norm_num

end AxiomaticGWTest.GKM.GenusTwoHodgeGeometricVertex
