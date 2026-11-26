/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneUniform

/-!
# A checked genus-one reconstruction step

The equation comes from the original Getzler presentation, its geometric
realization, and the existing surface reduction laws and degree-zero seeds.
The support theorem retains genus-zero terms at the original energy while
strictly decreasing the energy of every residual genus-one query.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

open SurfacePolynomialReduction SurfaceLowGenus

/-- Isolate the elliptic point invariant in an actual primary Getzler equation.
The uniform four-hyperplane family supplies the required nonzero coefficient
at every energy at least two. No numerical recurrence is assumed. -/
theorem primary_point_eq {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (hcoeff : RationalTerms.coefficient (primaryTerms X n beta 0 a)
      {pointVariable X 1 beta} ≠ 0)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (hp : AcceptsExchange p) :
    (SurfaceQuery.points X 1 beta (X.effective.energy beta)).eval U =
      -RationalTerms.eval (variableEval U P) (lowerTerms X beta (primaryTerms X n beta 0 a)) /
        RationalTerms.coefficient (primaryTerms X n beta 0 a) {pointVariable X 1 beta} := by
  have heq := exchange_checkedPrimaryTerms_eq_zero A I F N H hsource G hcycle
    Omega P T U S Hdiv hpair hH hE n houtput beta 0 a (primaryTerms X n beta 0 a)
    (fun _ _ ↦ rfl) p hp
  have hisolate := RationalTerms.eval_isolate_singleton (variableEval U P)
    (primaryTerms X n beta 0 a) (pointVariable X 1 beta)
  rw [heq] at hisolate
  simp only [Algebra.algebraMap_self_apply, pointVariable, variableEval,
    Nat.add_sub_cancel] at hisolate
  apply (eq_div_iff hcoeff).mpr
  rw [mul_comm]
  exact eq_neg_of_add_eq_zero_left hisolate.symm

end AxiomaticGW.GetzlerGraphs
