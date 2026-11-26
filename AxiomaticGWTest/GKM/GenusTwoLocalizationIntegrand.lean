import AxiomaticGW.GKM.Fixtures.GenusTwoHodgeSeedGeometry
import AxiomaticGW.GKM.Fixtures.ExceptionalDoubleCoverChain

/-! # Integrating the stable vertex of a doubled exceptional fixed locus -/

namespace AxiomaticGWTest.GKM.GenusTwoLocalizationIntegrand
open AxiomaticGW AxiomaticGW.GKM GenusTwoLocalizationClass GenusTwoVertexHodgeReduction
open GenusTwoHodgeSeedGeometry PsiBoundaryExpansion
open ExceptionalGenusTwoVertexValues (seed)
variable {C : StableCurveCohomology ℚ} {D : HodgeClasses C} {I : StableCurveIntegration C}

/-- The marked bivalent vertex at tangent weights 3 and 2 from source-curve geometry and the
seven matched Hodge integrals, including the sign in the two-character formula. -/
theorem bivalent_integral (H : D.Natural) (U : ForgetfulPushforward C I)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (P : PsiClasses C) (K : PsiForgetFormula P) (hK : TailCompatible K F N)
    (T : TailForgetCompatible C) (Q : ForgetfulSquareCompatibility U F)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)
    (base : P.kappa U 2 (Fin 0) (stable 0) 0 = 2)
    (square : (D.first 1 : C.H 2 (Fin 1)) ^ 2 = 2 * (D.second 1 : C.H 2 (Fin 1)))
    (seven : ∀ (i j : Fin 3), i ≤ j → ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ sevenKeys),
      seed ⟨_, (Finset.mem_erase.mp hk).2⟩ = moment D P I i j p) :
    integrate I _ (integrand D P [3] (3 : ℚ) 2 (fun _ : Fin 2 ↦ 3)) = -199/466560 := by
  rw [integrated_vertex H U F N P K hK T Q vol base square seven]
  change ExceptionalDoubleCoverChain.center [3] 3 2 = _
  rw [(ExceptionalDoubleCoverChain.center_eq (3 : ℚ) 2 (by decide) (by decide)).1]
  norm_num

end AxiomaticGWTest.GKM.GenusTwoLocalizationIntegrand
