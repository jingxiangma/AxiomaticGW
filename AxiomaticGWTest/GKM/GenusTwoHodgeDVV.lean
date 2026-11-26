import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeDVV
import AxiomaticGWTest.GKM.GenusTwoLocalizationIntegrand

/-! # The pure cotangent input and an integrated fixed-locus vertex from the DVV relation -/

namespace AxiomaticGWTest.GKM.GenusTwoHodgeDVV
open AxiomaticGW AxiomaticGW.GKM GenusTwoLocalizationClass GenusTwoVertexHodgeReduction
open AxiomaticGW.GKM.GenusTwoHodgeDVV PsiBoundaryExpansion
open ExceptionalGenusTwoVertexValues (seed)

variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C} {D : HodgeClasses C}

/-- The bivalent vertex with the four remaining Hodge comparisons and the original DVV input. -/
theorem bivalent (H : D.Natural) (U : ForgetfulPushforward C I)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (dvv : PointTarget.DVVRecursion P I)
    (one : I.integrate 1 (Fin 1) PointTarget.genusOne_one_stable
      (P.psi 1 _ PointTarget.genusOne_one_stable 0) = (1 / 24 : ℚ))
    (four : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ fourKeys),
      seed ⟨_, (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).2⟩ = moment D P I i j p) :
    integrate I _ (integrand D P [3] (3 : ℚ) 2 (fun _ : Fin 2 ↦ 3)) = -199/466560 :=
  AxiomaticGWTest.GKM.GenusTwoLocalizationIntegrand.bivalent_integral H U F N P K hK T Q vol
    base square (seven_from_DVV P I dvv vol one four)

/-- A partial expansion retains its unresolved request before applying a DVV step. -/
example : PointTarget.DVVCalculation.expand 0 2 [4] = RationalTerms.term 1 {(2, [4])} := rfl

end AxiomaticGWTest.GKM.GenusTwoHodgeDVV
