/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroSupport

/-!
# A checked genus-zero reconstruction step

The equation is derived from the original WDVV presentation and the existing
geometric laws. Its pivot is the exact coefficient in the complete graph
expansion, not a supplied recurrence coefficient. A nonzero-pivot proof permits
division, and the support theorem proves that all remaining queries decrease.
Uniform nonvanishing for a chosen family of requests is a separate obligation.
-/

@[expose] public section

namespace AxiomaticGW.WDVV

open SurfacePolynomialReduction SurfaceGenusZero

/-- Solve an actual primary WDVV request at its exact nonzero coefficient.
`wdvv_lowerTerms_dependencies` proves strict decrease of every residual query.
Neither the final numerical recurrence nor any additional seed is assumed. -/
theorem primary_point_eq {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (hboundary : BoundaryClassesEqual F)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (hcoeff : RationalTerms.coefficient (primaryTerms X n beta 0 a) {pointVariable X beta} ≠ 0)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : AcceptsExchange p) :
    (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U =
      -RationalTerms.eval (variableEval U P) (lowerTerms X beta (primaryTerms X n beta 0 a)) /
        RationalTerms.coefficient (primaryTerms X n beta 0 a) {pointVariable X beta} := by
  have heq := exchange_checkedPrimaryTerms_eq_zero A I F N H hsource hboundary
    Omega P T U S Hdiv hpair n houtput beta 0 a (primaryTerms X n beta 0 a)
    (fun _ _ ↦ rfl) p hp
  have hisolate := RationalTerms.eval_isolate_singleton (variableEval U P)
    (primaryTerms X n beta 0 a) (pointVariable X beta)
  rw [heq] at hisolate
  simp only [Algebra.algebraMap_self_apply, pointVariable, variableEval] at hisolate
  apply (eq_div_iff hcoeff).mpr
  rw [mul_comm]
  exact eq_neg_of_add_eq_zero_left hisolate.symm

end AxiomaticGW.WDVV
