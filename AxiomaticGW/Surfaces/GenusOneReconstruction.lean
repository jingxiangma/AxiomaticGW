/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneRecursion
public import AxiomaticGW.Surfaces.GenusZeroReconstruction
public import AxiomaticGW.Surfaces.Exceptional
public import AxiomaticGW.Surfaces.StrictLine

/-!
# Sound primary genus-one reconstruction from the finite seeds

Energy-one classes are exactly the exceptional generators and, on the two-point
blowup, the strict line. Their elliptic values follow from the existing checked
WDVV and Getzler equations, without enlarging the seed package. Together with
genus-zero reconstruction and the uniform Getzler pivot, this identifies the
terminating point function with every supplied geometric theory satisfying
the named inputs, and reconstructs arbitrary primary basis multisets.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

open SurfacePolynomialReduction SurfaceLowGenus
open SurfaceGenusZero (variableCurve pointLabels)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (I : StableCurveIntegration C)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hWsource : ∀ i, (WDVV.expression i).Compatible A F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
  (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
  (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
  (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
  (hpG : GetzlerGraphs.AcceptsExchange pG)
  (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)
  (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
  (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
  (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
  (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)

include A F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG P T S Hdiv hpair
  hline hEzero hH hE

/-- The full initial elliptic sector follows from the original finite seeds.
The zero-class empty query is explicitly the existing auxiliary convention. -/
theorem initialValue_eq_eval (beta : X.Curve) (hinit : IsInitial X beta) :
    (SurfaceQuery.points X 1 beta (X.effective.energy beta)).eval U = 0 := by
  by_cases hzero : beta = 0
  · subst beta
    rw [map_zero]
    apply U.invariant_zero_of_unstable
    change ¬StableArity 1 (Fin 0)
    unfold StableArity
    decide +kernel
  have hmem : beta ∈ X.bounded 1 := by
    rw [SurfaceTarget.bounded_eq, X.effective.mem_bounded]
    exact hinit
  cases X with
  | plane =>
      have hcover : ∀ b ∈ SurfaceTarget.plane.bounded 1, b = 0 := by decide +kernel
      exact (hzero (hcover beta hmem)).elim
  | hirzebruchOne =>
      have hcover : ∀ b ∈ SurfaceTarget.hirzebruchOne.bounded 1,
          b = 0 ∨ b = ![1, 0] := by decide +kernel
      rcases hcover beta hmem with hb | hb
      · exact (hzero hb).elim
      · subst beta
        have he := SurfaceExceptional.genusOne_exceptional A I F N H hGsource G hcycle
          Omega P T U S Hdiv hpair hH hE pG hpG 0 (hEzero 0)
        rw [show SurfaceTarget.hirzebruchOne.exceptionalCurve 0 = ![1, 0]
          from by decide +kernel] at he
        exact he
  | blowupTwo =>
      have hcover : ∀ b ∈ SurfaceTarget.blowupTwo.bounded 1,
          b = 0 ∨ b = ![1, 0, 0] ∨ b = ![0, 1, 0] ∨ b = ![0, 0, 1] := by decide +kernel
      have he (i : Fin 2) := SurfaceExceptional.genusOne_exceptional A I F N H hGsource G hcycle
        Omega P T U S Hdiv hpair hH hE pG hpG i (hEzero i)
      rcases hcover beta hmem with hb | hb | hb | hb
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
        exact (SurfaceStrictLine.baseCases A I F N H hWsource hboundary pW hpW hGsource G hcycle
          pG hpG Omega P T U S Hdiv hpair hline hEzero hH hE).2.2

/-- The terminating elliptic point computation agrees with the supplied theory,
at every full effective class, under the original finite seed and geometric inputs. -/
theorem pointValue_eq_eval
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) : pointValue X beta =
      (SurfaceQuery.points X 1 beta (X.effective.energy beta)).eval U := by
  symm
  apply eq_pointValue_of_equations X
    (fun b ↦ (SurfaceQuery.points X 1 b (X.effective.energy b)).eval U)
  · exact initialValue_eq_eval A I F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG
      Omega P T U S Hdiv hpair hline hEzero hH hE
  · intro b hb
    have heq := GetzlerGraphs.primary_point_eq A I F N H hGsource G hcycle
      Omega P T U S Hdiv hpair hH hE (X.effective.energy b - 2) (hGoutput _) b
      (pointLabels (GetzlerGraphs.reconstructionLabels X) (X.effective.energy b - 2))
      (reconstructionCoefficient_ne_zero X b hb) pG hpG
    change (SurfaceQuery.points X 1 b (X.effective.energy b)).eval U =
      -RationalTerms.eval (variableEval U P) (reconstructionRemainder X b) /
        reconstructionCoefficient X b at heq
    rw [heq]
    congr 2
    apply RationalTerms.eval_congr
    intro t ht v hv
    obtain ⟨g, gamma, _, rfl, hg, _⟩ := reconstructionRemainder_dependencies X b t ht v hv
    rw [pointValuation_point]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with hg | hg
    · subst g
      rw [if_pos rfl]
      exact (SurfaceGenusZero.pointValue_eq_eval A I F N H hWsource hboundary pW hpW
        Omega P T U S Hdiv hpair hline hEzero hWoutput gamma).symm
    · subst g
      rw [if_neg Nat.one_ne_zero]
      rfl

/-- Arbitrary primary genus-one basis multisets follow from the same inputs,
including degree zero, units, repeated divisors, and exceptional curve classes. -/
theorem primaryValue_eq_eval
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (m : Multiset (SurfaceBasisLabel X)) :
    primaryValue X beta m = SurfacePrimary.eval U 1 beta m := by
  by_cases hzero : beta = 0
  · subst beta
    rw [primaryValue, if_pos rfl]
    exact (SurfacePrimary.eval_genus_one_zero U T S Hdiv hH hE m).symm
  · rw [primaryValue, if_neg hzero, SurfacePrimary.eval_reduced U T S Hdiv hpair 1 beta hzero]
    by_cases hn : m.count .point = X.effective.energy beta
    · rw [if_pos hn, hn,
        pointValue_eq_eval A I F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG
          Omega P T U S Hdiv hpair hline hEzero hH hE hWoutput hGoutput,
        SurfaceQuery.eval_points]
    · rw [if_neg hn, SurfacePrimary.pointInvariant_eq_zero_of_dimension_ne U T 1 beta _ ?_,
        mul_zero]
      change (m.count .point : ℤ) ≠ (X.effective.energy beta : ℤ) + 1 - 1
      omega

end AxiomaticGW.SurfaceGenusOne
