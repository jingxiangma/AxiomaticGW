/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.ExceptionalGetzler

/-!
# Exceptional-class values deduced from Getzler's relation

The checked HHHH and HEᵢEᵢEᵢ equations first give the two double-class
vanishings. HHEᵢEᵢ then determines the genus-one one-point invariant of Eᵢ
from the existing seed N₀(Eᵢ) = 1. These are conditional deductions under
the existing geometric laws and finite seeds, not additional seed axioms.
The theorem ranges over E on F₁ and E₁,E₂ on the two-point blowup; it makes
no claim about the latter surface's distinct class L = H−E₁−E₂.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceExceptional

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (I : StableCurveIntegration C)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
  (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
  (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)
  (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
  (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
  (p : RelationCertificate.Presentation 1 (Fin 4) 1 33)
  (haccept : GetzlerGraphs.AcceptsExchange p)

include A F N H hsource G hcycle P T S Hdiv hpair hH hE p haccept

private theorem checkedEquation (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X)
    (result : RationalTerms (SurfacePolynomialReduction.Variable X))
    (hterms : RationalTerms.Equivalent (GetzlerGraphs.primaryTerms X 0 beta 0 a) result) :
    RationalTerms.eval (SurfacePolynomialReduction.variableEval U P) result = 0 := by
  apply GetzlerGraphs.exchange_checkedPrimaryTerms_eq_zero A I F N H hsource G hcycle
    Omega P T U S Hdiv hpair hH hE 0 ?_ beta 0 a result hterms p haccept
  intro i z hz
  simp only [GluingExpression.addMarkings, List.mem_singleton] at hz
  subst z
  exact hsource i

/-- The genus-one two-point invariant of twice an exceptional class is zero. -/
theorem genusOne_doubleExceptional (i : Fin X.blowups) :
    (SurfaceQuery.points X 1 (2 • X.exceptionalCurve i) 2).eval U = 0 := by
  have h := checkedEquation A I F N H hsource G hcycle Omega P T U S Hdiv hpair hH hE
    p haccept (2 • X.exceptionalCurve i) (fun _ ↦ .hyperplane)
    (SurfaceExceptionalGetzler.hyperplaneTerms X i)
    (SurfaceExceptionalGetzler.hyperplaneTerms_accepted X i)
  simp only [SurfaceExceptionalGetzler.hyperplaneTerms, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The genus-zero one-point invariant of twice an exceptional class is zero. -/
theorem genusZero_doubleExceptional (i : Fin X.blowups) :
    (SurfaceQuery.points X 0 (2 • X.exceptionalCurve i) 1).eval U = 0 := by
  have h := checkedEquation A I F N H hsource G hcycle Omega P T U S Hdiv hpair hH hE
    p haccept (2 • X.exceptionalCurve i)
    ![.hyperplane, .exceptional i, .exceptional i, .exceptional i]
    (SurfaceExceptionalGetzler.oneHyperplaneTerms X i)
    (SurfaceExceptionalGetzler.oneHyperplaneTerms_accepted X i)
  simp only [SurfaceExceptionalGetzler.oneHyperplaneTerms, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The existing exceptional seed and the three checked equations give
the genus-one one-point value without enlarging the finite seed package. -/
theorem genusOne_exceptional (i : Fin X.blowups)
    (hseed : (SurfaceSeed.exceptional i).query.eval U = 1) :
    (SurfaceQuery.points X 1 (X.exceptionalCurve i) 1).eval U = 0 := by
  have h := checkedEquation A I F N H hsource G hcycle Omega P T U S Hdiv hpair hH hE
    p haccept (2 • X.exceptionalCurve i)
    ![.hyperplane, .hyperplane, .exceptional i, .exceptional i]
    (SurfaceExceptionalGetzler.twoHyperplaneTerms X i)
    (SurfaceExceptionalGetzler.twoHyperplaneTerms_accepted X i)
  have h0 := genusZero_doubleExceptional A I F N H hsource G hcycle Omega P T U S
    Hdiv hpair hH hE p haccept i
  have h1 := genusOne_doubleExceptional A I F N H hsource G hcycle Omega P T U S
    Hdiv hpair hH hE p haccept i
  have hs : (SurfaceQuery.points X 0 (X.exceptionalCurve i) 0).eval U = 1 := hseed
  simp only [SurfaceExceptionalGetzler.twoHyperplaneTerms, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_coe, Multiset.prod_coe, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply,
    SurfacePolynomialReduction.variableEval, hs, h0, h1, one_mul, mul_one,
    mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end AxiomaticGW.SurfaceExceptional
