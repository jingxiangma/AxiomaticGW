/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiSupport

/-!
# Direct normalization of primary and first-power descendants

At genus at least two, the direct normalization interprets stable-map
descendants with total cotangent power at most one. This statement uses
string, dilaton and divisor laws; it does not identify nonzero ancestor
powers with descendant powers. Ancestor interpretation still requires the
separate rational-tail comparison.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceAncestorKey

/-- Primary insertion data have the same full numerical interpretation in
the descendant key and the existing primary multiset interface. -/
theorem descendantEval_eq_primary {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (q : SurfaceAncestorKey X) (hp : q.IsPrimary) :
    q.descendantEval U = SurfacePrimary.eval U q.genus q.beta q.primaryLabels := by
  have hk : (fun s : q.insertions ↦ (s : SurfaceInsertion X).psi) = (fun _ ↦ 0) := by
    funext s
    exact hp _ Multiset.coe_mem
  simp only [descendantEval, primaryLabels, SurfacePrimary.eval_map, hk]

end SurfaceAncestorKey

namespace SurfacePolynomialReduction

/-- Direct normalization is the actual low-power descendant invariant,
including degree zero and repeated primary insertions. -/
theorem eval_directNormalizedTerms_descendant
    {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (q : SurfaceAncestorKey X) (hg : 2 ≤ q.genus) (hk : q.totalPsi ≤ 1) :
    RationalTerms.eval (variableEval U P) (directNormalizedTerms q) =
      q.descendantEval U := by
  unfold directNormalizedTerms
  split_ifs with h
  · rw [RationalTerms.eval_rename]
    change RationalTerms.eval (SurfaceQuery.eval U) _ = _
    rw [SurfaceFirstDescendant.eval_terms U T laws H hpair q.genus hg]
    exact ((q.descendantEval_eq_query U).trans (q.descendantQuery_eq_first U h.2)).symm
  · have hz : q.totalPsi = 0 := by
      have hne : q.totalPsi ≠ 1 := fun he ↦ h ⟨hg, he⟩
      omega
    have hp := q.totalPsi_eq_zero_iff.mp hz
    rw [canonicalPrimaryTerms, if_pos ⟨hg, hp⟩, RationalTerms.eval_rename]
    change RationalTerms.eval (SurfaceQuery.eval U) _ = _
    rw [SurfaceFirstDescendant.eval_primaryTerms U T laws H hpair q.genus hg]
    exact (q.descendantEval_eq_primary U hp).symm

end SurfacePolynomialReduction

end AxiomaticGW
