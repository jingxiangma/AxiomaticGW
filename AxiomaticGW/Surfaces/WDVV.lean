/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.WDVVForgetful
public import AxiomaticGW.Surfaces.TermExpansion

/-!
# Complete reduced surface WDVV equations

The original three marked boundary columns use the existing full-class and
signed inverse-metric evaluator. Arbitrary additional markings and powers
retain their component assignments. The established primary reductions act
only where applicable. A checked term identity transfers the original WDVV
certificate to an equation in the supplied theory's actual invariants.
-/

@[expose] public section

namespace AxiomaticGW.WDVV

/-- Exact term expansion of the fixed WDVV request with all added markings. -/
def primaryTerms (X : SurfaceTarget)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms (SurfacePolynomialReduction.Variable X) :=
  ∑ i, RationalTerms.scale (requested i)
    ((((expression i).addMarkings n).map fun z ↦
      z.surfaceTerms X (SurfacePolynomialReduction.primaryVertexTerms X) beta k a).sum)

/-- The incoming WDVV certificate and an exact check against the full graph
request give the proposed reduced equation, under the existing geometric laws. -/
theorem exchange_checkedPrimaryTerms_eq_zero {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
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
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (result : RationalTerms (SurfacePolynomialReduction.Variable X))
    (hterms : RationalTerms.Equivalent (primaryTerms X n beta k a) result)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : AcceptsExchange p) :
    RationalTerms.eval (SurfacePolynomialReduction.variableEval U P) result = 0 := by
  rw [← RationalTerms.eval_eq_of_equivalent _ _ _ hterms]
  simpa only [primaryTerms, RationalTerms.eval_sum, RationalTerms.eval_scale,
    RationalTerms.eval_list_sum, List.map_map, Function.comp_def,
    GluingExpression.eval_primaryTerms_of_genus_zero U P T S Hdiv hpair,
    Algebra.algebraMap_self_apply, gwAncestorChannelWithMarkings] using
    exchange_ancestor_with_markings_eq_zero A F N hsource H hboundary Omega P n houtput
      beta k (fun s ↦ (a s).value) p hp

end AxiomaticGW.WDVV
