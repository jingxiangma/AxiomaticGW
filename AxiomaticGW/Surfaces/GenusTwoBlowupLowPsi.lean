/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowPsiDescendant
public import AxiomaticGW.Surfaces.GenusTwoBlowupRecursion

/-!
# Genus-two primary and first-power values on the blowups

Direct normalization reduces stable-map descendants to the canonical H/P/N/K
queries at the exact full curve class. Full ancestor normalization additionally
retains every signed first-calibration tail at an effective subclass. The two
polynomials are evaluated separately; no plane-only tail cancellation is used.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupLowPsi
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}

/-- Evaluate direct low-power descendant normalization against a full canonical table. -/
def descendantValueWith (values : State X → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  RationalTerms.eval (canonicalValuation values) (directNormalizedTerms q)

/-- Evaluate complete low-power ancestor normalization, retaining all calibration tails. -/
def ancestorValueWith (values : State X → ℚ) (q : SurfaceAncestorKey X) : ℚ :=
  RationalTerms.eval (canonicalValuation values) (normalizedTerms q)

/-- Direct normalization consults only the canonical table at the exact input class. -/
theorem descendantValueWith_congr (values other : State X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (h : ∀ f : Family X, values (q.beta, f) = other (q.beta, f)) :
    descendantValueWith values q = descendantValueWith other q := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  obtain ⟨c, hc, hm⟩ := directNormalizedTerms_canonical_support q hg hk ht
  obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hc
  rw [hm, Multiset.mem_singleton] at hx
  subst x
  rw [← hf, canonicalValuation_query, canonicalValuation_query]
  exact h f

/-- Full normalization consults canonical states at full effective subclasses.
The equality premise retains each subclass and exceptional label separately. -/
theorem ancestorValueWith_congr (values other : State X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (h : ∀ beta : X.Curve, (∃ delta : X.Curve, beta + delta = q.beta) →
      ∀ f : Family X, values (beta, f) = other (beta, f)) :
    ancestorValueWith values q = ancestorValueWith other q := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  obtain ⟨beta, c, hc, hm, delta, hsplit⟩ := normalizedTerms_canonical_support q hg hk ht
  obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hc
  rw [hm, Multiset.mem_singleton] at hx
  subst x
  rw [← hf, canonicalValuation_query, canonicalValuation_query]
  exact h beta ⟨delta, hsplit⟩ f

/-- Primary data have no first-calibration correction, so both polynomial evaluations agree. -/
theorem ancestorValueWith_eq_descendantValueWith_of_primary (values : State X → ℚ)
    (q : SurfaceAncestorKey X) (hp : q.IsPrimary) :
    ancestorValueWith values q = descendantValueWith values q := by
  have hz : q.totalPsi = 0 := q.totalPsi_eq_zero_iff.mpr hp
  have hn : ¬(2 ≤ q.genus ∧ q.totalPsi = 1) := by
    intro h
    omega
  simp only [ancestorValueWith, descendantValueWith, normalizedTerms, directNormalizedTerms,
    dif_neg hn]

section Interpretation
variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Canonical query equality interprets the complete direct polynomial as descendants. -/
theorem descendantValueWith_eval (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (values : State X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (hv : ∀ f : Family X, values (q.beta, f) = (f.query q.beta).eval U) :
    descendantValueWith values q =
      RationalTerms.eval (variableEval U P) (directNormalizedTerms q) := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  obtain ⟨c, hc, hm⟩ := directNormalizedTerms_canonical_support q hg hk ht
  obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hc
  rw [hm, Multiset.mem_singleton] at hx
  subst x
  rw [← hf, canonicalValuation_query]
  exact hv f

/-- Canonical query equality at every effective subclass interprets the full ancestor
polynomial without deleting its signed calibration corrections. -/
theorem ancestorValueWith_eval (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (values : State X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (hv : ∀ beta : X.Curve, (∃ delta : X.Curve, beta + delta = q.beta) →
      ∀ f : Family X, values (beta, f) = (f.query beta).eval U) :
    ancestorValueWith values q =
      RationalTerms.eval (variableEval U P) (normalizedTerms q) := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  obtain ⟨beta, c, hc, hm, delta, hsplit⟩ := normalizedTerms_canonical_support q hg hk ht
  obtain ⟨f, hf⟩ := family_of_mem_canonicalQueries hc
  rw [hm, Multiset.mem_singleton] at hx
  subst x
  rw [← hf, canonicalValuation_query]
  exact hv beta ⟨delta, hsplit⟩ f

end Interpretation

/-- Retain every ordered query occurrence in the existing insertion-multiset adapter. -/
def queryKey (q : SurfaceQuery X) (hg : q.genus = 2) : SurfaceAncestorKey X :=
  SurfaceAncestorKey.ofLabels q.genus (Fin q.insertions.length)
    (by simp only [StableArity, hg]; omega) q.beta
    (fun j ↦ (q.insertions.get j).psi) (fun j ↦ (q.insertions.get j).label)

/-- The terminating canonical reconstruction evaluates direct descendants. -/
def descendantValue (i : Fin X.blowups) (q : SurfaceAncestorKey X) : ℚ :=
  descendantValueWith (SurfaceGenusTwoBlowupRecursion.values i) q

/-- The terminating canonical reconstruction evaluates the complete ancestor polynomial. -/
def ancestorValue (i : Fin X.blowups) (q : SurfaceAncestorKey X) : ℚ :=
  ancestorValueWith (SurfaceGenusTwoBlowupRecursion.values i) q

/-- Reconstruct the supplied ordered descendant query through the occurrence adapter. -/
def queryValue (i : Fin X.blowups) (q : SurfaceQuery X) (hg : q.genus = 2)
    (_hk : (∑ j : Fin q.insertions.length, (q.insertions.get j).psi) ≤ 1) : ℚ :=
  descendantValue i (queryKey q hg)

section Geometry
variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (i : Fin X.blowups) (U : UnstableDescendantConventions M I) (P : PsiClasses C)
  (T : SurfaceTheoryIdentification X Omega)
  (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
  (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
  (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
    -1 / 2880)
  (hBP : ∀ n beta a, RationalTerms.eval (variableEval U P)
    (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0)
  (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel X),
    RationalTerms.eval (variableEval U P) (L24Relation.normalizedGenusTwoTerms X n beta 0
      (SurfaceGenusZero.pointLabels a n)) = 0)
  (laws : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible A)

include i U P T V hV hHtwo hEtwo hBP hL laws H hpair

/-- Arbitrary primary and first-power descendants follow from the original unsolved
BP/L24 equations, finite divisor seeds, exceptional support and descendant laws. -/
theorem descendantValue_from_original_equations
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1) :
    descendantValue i q = q.descendantEval U := by
  have he := descendantValueWith_eval U P
    (SurfaceGenusTwoBlowupRecursion.values i) q hg hk (fun f ↦
      SurfaceGenusTwoBlowupRecursion.values_eq_eval_of_original_equations i U P T V hV
        hHtwo hEtwo hBP hL (q.beta, f))
  exact he.trans (eval_directNormalizedTerms_descendant U P T laws H hpair q (by omega) hk)

/-- Ordered low-power descendant requests have the checked reconstructed value.
Every repeated label and cotangent occurrence is retained by the query adapter. -/
theorem queryValue_checkedEval_from_original_equations
    (q : SurfaceQuery X) (hg : q.genus = 2)
    (hk : (∑ j : Fin q.insertions.length, (q.insertions.get j).psi) ≤ 1) :
    q.checkedEval U = some (queryValue i q hg hk) := by
  have hkey : (queryKey q hg).genus = 2 := hg
  have hpower : (queryKey q hg).totalPsi ≤ 1 := by
    simpa only [queryKey, SurfaceAncestorKey.totalPsi_ofLabels] using hk
  have hv := descendantValue_from_original_equations i U P T V hV hHtwo hEtwo hBP hL
    laws H hpair (queryKey q hg) hkey hpower
  have he : (queryKey q hg).descendantEval U = q.eval U :=
    SurfaceAncestorKey.descendantEval_ofLabels U _ _ _ _ _ _
  have hd : q.GeometricDomain := Or.inr (by simp only [StableArity, hg]; omega)
  rw [SurfaceQuery.checkedEval_of_geometricDomain U q hd]
  exact congrArg some (hv.trans he).symm

variable
  (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (J : GluingForgetfulCompatibility F N)
  (hWsource : ∀ j, (WDVV.expression j).Compatible Z F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
  (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
  (hE : ∀ j, (SurfaceSeed.exceptional j : SurfaceSeed X).query.eval U = 1)
  (hWoutput : ∀ n j z, z ∈ (WDVV.expression j).addMarkings n → z.Compatible Z F N)
  {St : StableMapStabilization V} (RT : RationalTailIntersection V St P)

include Z F N J hWsource hboundary pW hpW hline hE hWoutput RT

/-- Full first-power ancestors use the entire signed calibration polynomial.
WDVV and rational-tail geometry produce its calibration, while the original
BP/L24 equations and finite seeds reconstruct every canonical subclass value. -/
theorem ancestorValue_from_original_equations
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1) :
    ancestorValue i q = q.eval Omega P I := by
  have he := ancestorValueWith_eval U P
    (SurfaceGenusTwoBlowupRecursion.values i) q hg hk (fun beta _ f ↦
      SurfaceGenusTwoBlowupRecursion.values_eq_eval_of_original_equations i U P T V hV
        hHtwo hEtwo hBP hL (beta, f))
  exact he.trans (eval_normalizedTerms U P T laws H hpair Z F N J hWsource hboundary
    pW hpW hline hE hWoutput RT q)

end Geometry

end AxiomaticGW.SurfaceGenusTwoBlowupLowPsi
