/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DegreeZero
public import AxiomaticGW.Surfaces.PolynomialReduction

/-!
# Degree-zero substitution in surface reconstruction equations

The primary degree-zero sectors in genera zero and one now evaluate to
constants using the existing string/divisor laws and finite elliptic seeds.
They can be substituted after positive-class reduction. Other genera, powers,
and numerical queries retain their existing semantics without an extra rule.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfacePolynomialReduction

/-- A known degree-zero constant, or `none` when this rule does not apply.
Only primary ancestors in genera zero and one are evaluated. -/
def degreeZeroValue? {X : SurfaceTarget} : Variable X → Option ℚ
  | .inl q =>
      if q.beta = 0 ∧ q.IsPrimary then
        if q.genus = 0 then some (SurfacePrimary.classicalValue q.primaryLabels)
        else if q.genus = 1 then some (SurfacePrimary.genusOneZeroValue q.primaryLabels)
        else none
      else none
  | .inr _ => none

/-- Substitute a known constant and otherwise retain the original variable. -/
noncomputable def degreeZeroPolynomial {X : SurfaceTarget} (v : Variable X) :
    MvPolynomial (Variable X) ℚ :=
  match degreeZeroValue? v with
  | some c => MvPolynomial.C c
  | none => MvPolynomial.X v

/-- Simultaneous genus-zero/one degree-zero primary substitution. -/
noncomputable def reduceDegreeZero (X : SurfaceTarget) :
    MvPolynomial (Variable X) ℚ →ₐ[ℚ] MvPolynomial (Variable X) ℚ :=
  MvPolynomial.aeval degreeZeroPolynomial

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Every degree-zero substitution is a theorem about the actual supplied
invariant. The only numerical inputs used are the finite elliptic divisor seeds. -/
theorem aeval_degreeZeroPolynomial (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (v : Variable X) :
    MvPolynomial.aeval (variableEval U P) (degreeZeroPolynomial v) = variableEval U P v := by
  cases v with
  | inr q => exact MvPolynomial.aeval_X _ _
  | inl q =>
      simp only [degreeZeroPolynomial, degreeZeroValue?]
      split_ifs with h hg0 hg1
      · simp only [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
          variableEval, SurfaceAncestorKey.eval_eq_primary U P q h.2, h.1, hg0]
        exact (SurfacePrimary.eval_genus_zero_zero U T S q.primaryLabels).symm
      · simp only [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
          variableEval, SurfaceAncestorKey.eval_eq_primary U P q h.2, h.1, hg1]
        exact (SurfacePrimary.eval_genus_one_zero U T S H hH hE q.primaryLabels).symm
      · exact MvPolynomial.aeval_X _ _
      · exact MvPolynomial.aeval_X _ _

/-- Degree-zero substitution preserves every polynomial in residual variables. -/
theorem aeval_reduceDegreeZero (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (p : MvPolynomial (Variable X) ℚ) :
    MvPolynomial.aeval (variableEval U P) (reduceDegreeZero X p) =
      MvPolynomial.aeval (variableEval U P) p := by
  rw [reduceDegreeZero, MvPolynomial.comp_aeval_apply]
  simp only [aeval_degreeZeroPolynomial U P T S H hH hE]

/-- The two reductions compose without changing the original ancestor
polynomial's invariant value. No extra classical cubic assumption is needed. -/
theorem aeval_reduceDegreeZero_reduce (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (p : MvPolynomial (SurfaceAncestorKey X) ℚ) :
    MvPolynomial.aeval (variableEval U P) (reduceDegreeZero X (reduce X p)) =
      MvPolynomial.aeval (SurfaceAncestorKey.eval Omega P I) p := by
  rw [aeval_reduceDegreeZero U P T S H hH hE, aeval_reduce U P T S H hpair]

end SurfacePolynomialReduction

namespace GetzlerGraphs

/-- The unchanged incoming Getzler certificate gives the equation with
dimension, positive-class primary, and genus-zero/one degree-zero rules applied. -/
theorem exchange_primarySurfacePolynomial_eq_zero {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
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
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (haccept : AcceptsExchange p) :
    MvPolynomial.aeval (SurfacePolynomialReduction.variableEval U P)
      (SurfacePolynomialReduction.reduceDegreeZero X
        (SurfacePolynomialReduction.reduce X (surfacePolynomial n beta k a))) = 0 := by
  rw [SurfacePolynomialReduction.aeval_reduceDegreeZero_reduce U P T S Hdiv hpair hH hE]
  exact exchange_surfacePolynomial_eq_zero A I F N H hsource G hcycle Omega P
    T.pairing_eq n houtput beta k a p haccept

end GetzlerGraphs

end AxiomaticGW
