/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Assembly
public import AxiomaticGW.Tautological.L24InitialClass

/-!
# The complete L24 realized class relation

The fixed 721-term vector is derived from the actual BP pullback, all 71
checked corrections and the prescribed marking average. Its primitive part
is not substituted for the full equation. The BP and four lower-arity
genus-two source relations, the two derived rational psi relations, and
primitive gluing/cotangent/WDVV geometry remain explicit inputs. Their
existing source theorems can supply these hypotheses; no new numerical
seed, final-row vanishing or intersection diagnostic is assumed.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open RelationCertificate GluingExpression

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- All 721 coefficients give a class relation from the identified original source operations. -/
theorem realized_full
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (H : PsiBoundaryExpansion.TailForgetCompatible C) (G : GluingForgetfulCompatibility F N)
    (hbp : (A 2 (Fin 3)).map BelorousskiPandharipande.paperRelation = 0)
    (hin : ∀ t ∈ L24Initial.bp, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hout : ∀ t ∈ L24Initial.bp, ∀ z ∈ t.2.addMarkings 1,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (hl : (A 2 (ExtraMarkings 1 (Fin 3))).RelabelCompatible (A 2 (Fin 4))
      (BelorousskiPandharipande.stableArity.extraMarkings 1) L24Symmetry.stableArity
      L24Initial.labels)
    (hp : (A 2 (Fin 4)).LegPsiCompatible P L24Symmetry.stableArity)
    (hs : ∀ p, (A 2 (Fin 4)).RelabelCompatible (A 2 (Fin 4))
      L24Symmetry.stableArity L24Symmetry.stableArity (L24Symmetry.labels p))
    (hhigh : L24HighPsi.Compatible A F P)
    (hs2 : (A 2 (Fin 2)).map GenusTwoPsiPullbacks.squareTwo.strata = 0)
    (hs3 : (A 2 (Fin 3)).map GenusTwoPsiPullbacks.squareThree.strata = 0)
    (hp2 : (A 2 (Fin 2)).map GenusTwoPsiProduct.cotangentRelation.strata = 0)
    (hp3 : (A 2 (Fin 3)).map GenusTwoPsiPullbacks.productThree.strata = 0)
    (hrational : L24RationalPsi.Compatible A F P)
    (hr4 : (A 0 (Fin 4)).map (interpret (RationalPsiRelation.columns 1)
      (RationalPsiRelation.coordinates 1)) = 0)
    (hr5 : (A 0 (Fin 5)).map (interpret (RationalPsiRelation.columns 2)
      (RationalPsiRelation.coordinates 2)) = 0)
    (hwdvv : L24WDVV.Compatible A F P)
    (hwsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hwboundary : WDVV.BoundaryClassesEqual F) :
    (A 2 (Fin 4)).map (interpret L24Graphs.columns L24CorrectionsReplay.fullClaim) = 0 := by
  have hi := L24InitialClass.initial_vanishes A F N P K hK H G hbp hin hout hl hp hs
  have hh := L24HighPsi.corrections_vanish A F P hhigh hs2 hs3 hp2 hp3
  have hr := L24RationalPsi.corrections_vanish A F P hrational hr4 hr5
  have hw := L24WDVV.corrections_vanish_from_geometry A F N P hwdvv hwsource hwboundary hs
  rw [← L24Assembly.assemble_interpret]
  exact L24Assembly.assemble_vanishes (A 2 (Fin 4)) hs _ hi hh hr hw

end AxiomaticGW.L24Relation
