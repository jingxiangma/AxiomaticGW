/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroTable
public import AxiomaticGW.Surfaces.BlowupGenusZero

/-!
# Sound genus-zero point reconstruction from the finite seeds

The complete initial sector follows from the existing line and exceptional
seeds and the original checked WDVV relation. In particular, double exceptional
and double strict-line vanishing are obtained directly from WDVV here; no
elliptic seed or Getzler hypothesis is needed. The well-founded computation
therefore agrees with every supplied surface theory satisfying these inputs.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

open SurfacePolynomialReduction

private theorem doubleExceptional_terms (X : SurfaceTarget) (i : Fin X.blowups) :
    RationalTerms.Equivalent
      (WDVV.primaryTerms X 0 (2 • X.exceptionalCurve i) 0
        ![.hyperplane, .hyperplane, .exceptional i, .exceptional i])
      (RationalTerms.term 4 {pointVariable X (2 • X.exceptionalCurve i)}) := by
  cases X <;> fin_cases i <;> decide +kernel

private theorem doubleStrictLine_terms :
    RationalTerms.Equivalent
      (WDVV.primaryTerms .blowupTwo 0 ![0, 0, 2] 0
        ![.hyperplane, .hyperplane, .exceptional 0, .exceptional 1])
      (RationalTerms.term 4 {pointVariable .blowupTwo ![0, 0, 2]}) := by
  decide +kernel

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (I : StableCurveIntegration C)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
  (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)

include A F N H hsource hboundary p hp P T S Hdiv hpair

private theorem point_eq_zero_of_terms (beta : X.Curve) (a : Fin 4 → SurfaceBasisLabel X)
    (hterms : RationalTerms.Equivalent (WDVV.primaryTerms X 0 beta 0 a)
      (RationalTerms.term 4 {pointVariable X beta})) :
    (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U = 0 := by
  have heq := WDVV.exchange_checkedPrimaryTerms_eq_zero A I F N H hsource hboundary
    Omega P T U S Hdiv hpair 0 (by
      intro i z hz
      simp only [GluingExpression.addMarkings, List.mem_singleton] at hz
      subst z
      exact hsource i) beta 0 a (RationalTerms.term 4 {pointVariable X beta}) hterms p hp
  simp only [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton,
    Algebra.algebraMap_self_apply, pointVariable, variableEval] at heq
  exact (mul_eq_zero.mp heq).resolve_left (by norm_num)

/-- WDVV alone proves the double-exceptional genus-zero vanishing on both blowups. -/
theorem doubleExceptional_eq_zero (i : Fin X.blowups) :
    (SurfaceQuery.points X 0 (2 • X.exceptionalCurve i)
      (X.effective.energy (2 • X.exceptionalCurve i) - 1)).eval U = 0 :=
  point_eq_zero_of_terms A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
    (2 • X.exceptionalCurve i) _ (doubleExceptional_terms X i)

/-- The full initial table is derived from the original relation and the existing finite seeds. -/
theorem initialValue_eq_eval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (beta : X.Curve) (hinit : IsInitial X beta) :
    (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U =
      initialValue X beta := by
  by_cases hzero : beta = 0
  · subst beta
    rw [show initialValue X 0 = 0 from by cases X <;> decide +kernel, map_zero]
    apply U.invariant_zero_of_unstable
    change ¬StableArity 0 (Fin 0)
    unfold StableArity
    decide +kernel
  by_cases hlineclass : beta = X.lineCurve
  · subst beta
    rw [initialValue.eq_def, if_pos rfl,
      show X.effective.energy X.lineCurve = 3 from by cases X <;> decide +kernel]
    exact hline
  have hsmall : X.effective.energy beta ≤ 2 := hinit.resolve_right hlineclass
  have hmem : beta ∈ X.bounded 2 := by
    rw [SurfaceTarget.bounded_eq, X.effective.mem_bounded]
    exact hsmall
  cases X with
  | plane =>
      have hcover : ∀ b ∈ SurfaceTarget.plane.bounded 2, b = 0 := by decide +kernel
      exact (hzero (hcover beta hmem)).elim
  | hirzebruchOne =>
      have hcover : ∀ b ∈ SurfaceTarget.hirzebruchOne.bounded 2,
          b = 0 ∨ b = ![1, 0] ∨ b = ![2, 0] ∨ b = ![0, 1] := by decide +kernel
      rcases hcover beta hmem with hb | hb | hb | hb
      · exact (hzero hb).elim
      · subst beta
        have he := hE 0
        change (SurfaceQuery.points .hirzebruchOne 0
          (SurfaceTarget.hirzebruchOne.exceptionalCurve 0) 0).eval U = 1 at he
        rw [show SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = ![1, 0]
          from by decide +kernel] at he
        exact he
      · subst beta
        have he := doubleExceptional_eq_zero A I F N H hsource hboundary p hp
          Omega P T U S Hdiv hpair 0
        rw [show 2 • SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = ![2, 0]
          from by decide +kernel] at he
        exact he
      · subst beta
        exact SurfaceBlowupGenusZero.hirzebruch_fiber A I F N H hsource hboundary p hp
          Omega P T U S Hdiv hpair hline (hE 0)
  | blowupTwo =>
      have hcover : ∀ b ∈ SurfaceTarget.blowupTwo.bounded 2,
          b = 0 ∨ b = ![1, 0, 0] ∨ b = ![0, 1, 0] ∨ b = ![0, 0, 1] ∨
          b = ![2, 0, 0] ∨ b = ![0, 2, 0] ∨ b = ![0, 0, 2] ∨
          b = ![1, 1, 0] ∨ b = ![1, 0, 1] ∨ b = ![0, 1, 1] := by decide +kernel
      have hbase := SurfaceBlowupGenusZero.blowup_baseCases A I F N H hsource hboundary p hp
        Omega P T U S Hdiv hpair hline hE
      have he (i : Fin 2) : (SurfaceQuery.points .blowupTwo 0
          (SurfaceTarget.blowupTwo.exceptionalCurve i) 0).eval U = 1 := hE i
      have hd (i : Fin 2) := doubleExceptional_eq_zero A I F N H hsource hboundary p hp
        Omega P T U S Hdiv hpair i
      rcases hcover beta hmem with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
      · exact (hzero hb).elim
      · subst beta
        have hh := he 0
        rw [show SurfaceTarget.blowupTwo.exceptionalCurve 0 = ![1, 0, 0]
          from by decide +kernel] at hh
        exact hh
      · subst beta
        have hh := he 1
        rw [show SurfaceTarget.blowupTwo.exceptionalCurve 1 = ![0, 1, 0]
          from by decide +kernel] at hh
        exact hh
      · subst beta
        exact hbase.1
      · subst beta
        have hh := hd 0
        rw [show 2 • SurfaceTarget.blowupTwo.exceptionalCurve 0 = ![2, 0, 0]
          from by decide +kernel] at hh
        exact hh
      · subst beta
        have hh := hd 1
        rw [show 2 • SurfaceTarget.blowupTwo.exceptionalCurve 1 = ![0, 2, 0]
          from by decide +kernel] at hh
        exact hh
      · subst beta
        exact point_eq_zero_of_terms A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
          ![0, 0, 2] _ doubleStrictLine_terms
      · subst beta
        exact hbase.2.2
      · subst beta
        have hh := hbase.2.1 0
        rw [show SurfaceTarget.blowupTwo.exceptionalCurve 0 + ![0, 0, 1] = ![1, 0, 1]
          from by decide +kernel] at hh
        exact hh
      · subst beta
        have hh := hbase.2.1 1
        rw [show SurfaceTarget.blowupTwo.exceptionalCurve 1 + ![0, 0, 1] = ![0, 1, 1]
          from by decide +kernel] at hh
        exact hh

/-- The terminating computation agrees with every actual point invariant of
the supplied theory, using only its line and exceptional genus-zero seeds.
At zero class this returns the existing auxiliary zero-point convention. -/
theorem pointValue_eq_eval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) : pointValue X beta =
      (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U := by
  symm
  apply eq_pointValue_of_equations X
    (fun b ↦ (SurfaceQuery.points X 0 b (X.effective.energy b - 1)).eval U)
  · exact initialValue_eq_eval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
      hline hE
  · intro b hb
    have heq := WDVV.primary_point_eq A I F N H hsource hboundary Omega P T U S Hdiv hpair
      (reconstructionRequest X b).1 (houtput _) b (reconstructionRequest X b).2
      (reconstructionCoefficient_ne_zero X b hb) p hp
    change (SurfaceQuery.points X 0 b (X.effective.energy b - 1)).eval U =
      -RationalTerms.eval (variableEval U P) (reconstructionRemainder X b) /
        reconstructionCoefficient X b at heq
    rw [heq]
    congr 2
    apply RationalTerms.eval_congr
    intro t ht v hv
    obtain ⟨gamma, _, rfl, _⟩ := reconstructionRemainder_dependencies X b t ht v hv
    rfl

/-- All primary genus-zero basis multisets are reconstructed, at arbitrary
marking count and full curve class, from the same finite genus-zero seeds. -/
theorem primaryValue_eq_eval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) :
    primaryValue X beta m = SurfacePrimary.eval U 0 beta m := by
  by_cases hzero : beta = 0
  · subst beta
    rw [primaryValue, if_pos rfl]
    exact (SurfacePrimary.eval_genus_zero_zero U T S m).symm
  · rw [primaryValue, if_neg hzero, SurfacePrimary.eval_reduced U T S Hdiv hpair 0 beta hzero]
    by_cases hn : m.count .point = X.effective.energy beta - 1
    · rw [if_pos hn, hn,
        pointValue_eq_eval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
          hline hE houtput, SurfaceQuery.eval_points]
    · rw [if_neg hn, SurfacePrimary.pointInvariant_eq_zero_of_dimension_ne U T 0 beta _ ?_,
        mul_zero]
      have he : 0 < X.effective.energy beta :=
        Nat.pos_of_ne_zero (fun h ↦ hzero ((X.effective.energy_eq_zero_iff beta).mp h))
      change (m.count .point : ℤ) ≠ (X.effective.energy beta : ℤ) + 0 - 1
      omega

/-- The bounded-table point computation has the same geometric soundness contract. -/
theorem cachedPointValue_eq_eval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) : cachedPointValue X beta =
      (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U :=
  (cachedPointValue_eq X beta).trans
    (pointValue_eq_eval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
      hline hE houtput beta)

/-- Certified table reuse also preserves every primary basis-multiset value. -/
theorem cachedPrimaryValue_eq_eval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) :
    cachedPrimaryValue X beta m = SurfacePrimary.eval U 0 beta m :=
  (cachedPrimaryValue_eq X beta m).trans
    (primaryValue_eq_eval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
      hline hE houtput beta m)

end AxiomaticGW.SurfaceGenusZero
