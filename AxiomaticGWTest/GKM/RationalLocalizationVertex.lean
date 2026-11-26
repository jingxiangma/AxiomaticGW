module

public import AxiomaticGW.GKM.RationalLocalizationVertex

/-! # Stable rational vertices with unequal cover weights and ordered markings -/

@[expose] public section
namespace AxiomaticGWTest.GKM.RationalLocalizationVertex
open AxiomaticGW AxiomaticGW.GKM.RationalLocalizationVertex PsiBoundaryExpansion

/-- At tangent characters 2 and 3, two covers of degree two give flags 3/2 and 1.
The native center has the two markings (0,1) and its incident flags have powers summing to one. -/
theorem mixed_flags {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1) :
    source ![0,1] (2 : ℚ) 3 ![2,3/2,1] (PointTarget.intersectionNumber P I 0 _) = 13 / 54 := by
  have hs : StableArity 0 (Fin 2 ⊕ Fin 3) := by unfold StableArity; decide
  rw [source_eq_closed U F N P K hK T vol hs]
  decide +kernel

/-- Constant-map flags and an excess cotangent insertion exercise both dimension boundaries. -/
example : closed ![0,0,0] (2 : ℚ) 3 ![] = 1 / 6 ∧ closed ![0,0,0,0] (2 : ℚ) 3 ![] = 0 ∧
    closed ![2,0,0,0] (2 : ℚ) 3 ![2,3/2] = 7 / 36 ∧ closed ![3] (2 : ℚ) 3 ![2,3/2] = 0 := by
  decide +kernel

end AxiomaticGWTest.GKM.RationalLocalizationVertex
