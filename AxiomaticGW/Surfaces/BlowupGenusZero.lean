/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupWDVV
public import Mathlib.Tactic.Linarith

/-!
# Ruling and strict-line values from the finite genus-zero seeds

The checked WDVV equations determine the F₁ fibre and the two rulings on the
two-point blowup. The latter calculation also determines N₀(L)=1 for the
distinct effective generator L=H−E₁−E₂ and the E₁+E₂ one-point vanishing.
Only the existing genus-zero line and exceptional seeds are used.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceBlowupGenusZero

variable {C : StableCurveCohomology ℚ}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (I : StableCurveIntegration C)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)

include A F N H hsource hboundary p hp

section General

variable {X : SurfaceTarget}
  (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)

include P T S Hdiv hpair

private theorem checkedEquation (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X)
    (result : RationalTerms (SurfacePolynomialReduction.Variable X))
    (hterms : RationalTerms.Equivalent (WDVV.primaryTerms X 0 beta 0 a) result) :
    RationalTerms.eval (SurfacePolynomialReduction.variableEval U P) result = 0 := by
  apply WDVV.exchange_checkedPrimaryTerms_eq_zero A I F N H hsource hboundary
    Omega P T U S Hdiv hpair 0 ?_ beta 0 a result hterms p hp
  intro i z hz
  simp only [GluingExpression.addMarkings, List.mem_singleton] at hz
  subst z
  exact hsource i

end General

section Hirzebruch

variable (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.hirzebruchOne.blowups)
    SurfaceTarget.hirzebruchOne.Curve SurfaceTarget.hirzebruchOne.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification .hirzebruchOne Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)

include P T S Hdiv hpair

/-- The one-point fibre invariant of F₁ is derived from its line and E seeds. -/
theorem hirzebruch_fiber
    (hline : (SurfaceSeed.line : SurfaceSeed .hirzebruchOne).query.eval U = 1)
    (hE : (SurfaceSeed.exceptional 0 : SurfaceSeed .hirzebruchOne).query.eval U = 1) :
    (SurfaceQuery.points .hirzebruchOne 0 ![0, 1] 1).eval U = 1 := by
  have h := checkedEquation A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
    ![1, 1] ![.hyperplane, .point, .exceptional 0, .exceptional 0]
    SurfaceBlowupWDVV.hirzebruchLine SurfaceBlowupWDVV.hirzebruchLine_accepted
  change (SurfaceQuery.points .hirzebruchOne 0 SurfaceTarget.hirzebruchOne.lineCurve 2).eval U
    = 1 at hline
  change (SurfaceQuery.points .hirzebruchOne 0
    (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) 0).eval U = 1 at hE
  rw [show SurfaceTarget.hirzebruchOne.lineCurve = ![1, 1] from by decide +kernel] at hline
  rw [show SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = ![1, 0] from by decide +kernel] at hE
  simp only [SurfaceBlowupWDVV.hirzebruchLine, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_coe, Multiset.prod_coe, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Multiset.map_singleton, Multiset.prod_singleton,
    Algebra.algebraMap_self_apply, SurfacePolynomialReduction.variableEval,
    hline, hE, one_mul, mul_one] at h
  linarith

end Hirzebruch

section BlowupTwo

variable (Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.blowupTwo.blowups)
    SurfaceTarget.blowupTwo.Curve SurfaceTarget.blowupTwo.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification .blowupTwo Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)

include P T S Hdiv hpair

/-- The four WDVV requests determine L, both rulings, and E₁+E₂.
The curve coordinates are the full ordered triple (E₁,E₂,L). -/
theorem blowup_baseCases
    (hline : (SurfaceSeed.line : SurfaceSeed .blowupTwo).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed .blowupTwo).query.eval U = 1) :
    (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0).eval U = 1 ∧
      (∀ i : Fin 2, (SurfaceQuery.points .blowupTwo 0
        (SurfaceTarget.blowupTwo.exceptionalCurve i + ![0, 0, 1]) 1).eval U = 1) ∧
      (SurfaceQuery.points .blowupTwo 0 ![1, 1, 0] 1).eval U = 0 := by
  have hmix := checkedEquation A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
    ![1, 1, 1] ![.hyperplane, .hyperplane, .point, .exceptional 0]
    SurfaceBlowupWDVV.mixedLine SurfaceBlowupWDVV.mixedLine_accepted
  have hl := checkedEquation A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
    ![1, 1, 1] ![.hyperplane, .point, .exceptional 0, .exceptional 0]
    SurfaceBlowupWDVV.line SurfaceBlowupWDVV.line_accepted
  have hr (i : Fin 2) := checkedEquation A I F N H hsource hboundary p hp Omega P T U S
    Hdiv hpair (SurfaceTarget.blowupTwo.exceptionalCurve i + ![0, 0, 1])
    ![.hyperplane, .hyperplane, .exceptional i, .exceptional i]
    (SurfaceBlowupWDVV.ruling i) (SurfaceBlowupWDVV.ruling_accepted i)
  have he : ∀ i, (SurfaceQuery.points .blowupTwo 0
      (SurfaceTarget.blowupTwo.exceptionalCurve i) 0).eval U = 1 := hE
  have he0 := he 0
  rw [show SurfaceTarget.blowupTwo.exceptionalCurve 0 = ![1, 0, 0] from by decide +kernel] at he0
  change (SurfaceQuery.points .blowupTwo 0 SurfaceTarget.blowupTwo.lineCurve 2).eval U = 1 at hline
  rw [show SurfaceTarget.blowupTwo.lineCurve = ![1, 1, 1] from by decide +kernel] at hline
  simp only [SurfaceBlowupWDVV.mixedLine, SurfaceBlowupWDVV.line, SurfaceBlowupWDVV.ruling,
    RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_coe, Multiset.prod_coe,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval, he, he0, hline, one_mul, mul_one] at hmix hl hr
  have hprod : (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0).eval U *
      (SurfaceQuery.points .blowupTwo 0 ![1, 1, 0] 1).eval U = 0 := by linarith
  have hf : (SurfaceQuery.points .blowupTwo 0 ![0, 1, 1] 1).eval U = 1 := by
    rw [hprod] at hl
    linarith
  have hr1 := hr 1
  rw [show SurfaceTarget.blowupTwo.exceptionalCurve 1 + ![0, 0, 1] = ![0, 1, 1]
    from by decide +kernel, hf] at hr1
  have hL : (SurfaceQuery.points .blowupTwo 0 ![0, 0, 1] 0).eval U = 1 := by linarith
  refine ⟨hL, fun i ↦ ?_, ?_⟩
  · have hi := hr i
    rw [hL] at hi
    linarith
  · simpa only [hL, one_mul] using hprod

end BlowupTwo

end AxiomaticGW.SurfaceBlowupGenusZero
