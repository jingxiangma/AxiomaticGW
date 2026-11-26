/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Terms
public import AxiomaticGW.Tautological.L24Relation

/-!
# The complete L24 GW equation with arbitrary added markings

The 721 nonzero coefficients keep their held raw normalization. Every column
has an actual decorated gluing, so primitive realization and GW gluing give
its full curve-class contraction. Signed universal-curve pullbacks preserve
node powers, negative tail corrections and repeated terms. The class input
is derived from the original BP/psi/WDVV geometry in `realized_full`.
This is a family of complete equations, not an assumed numerical recurrence.
-/

@[expose] public section

namespace AxiomaticGW.L24Relation
open RelationCertificate GluingExpression PsiBoundaryExpansion

-- Membership elimination reduces the same 815-column data as the graph replay.
set_option maxRecDepth 20000

universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- The full L24 family follows from the original class sources and primitive geometry.
All effective-class splittings, source node powers and upstairs ancestor powers survive. -/
theorem gw_forget_relation_from_geometry
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
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
    (hwboundary : WDVV.BoundaryClassesEqual F)
    (n : ℕ) (hterms : ∀ t ∈ cotangentRelation,
      t.2.expression.Compatible A F N ∧ t.2.expression.CotangentCompatible A P)
    (hadded : ∀ t ∈ cotangentRelation, ∀ z ∈ t.2.addMarkings n,
      z.2.expression.Compatible A F N ∧ z.2.expression.CotangentCompatible A P)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → V) :
    (cotangentRelation.pullback n).gwContraction Omega P I beta k a = 0 := by
  have hz : (A 2 (Fin 4)).map cotangentRelation.strata = 0 := by
    rw [cotangentRelation_strata]
    exact realized_full A F N P K hK H G hbp hin hout hl hp hs hhigh hs2 hs3 hp2 hp3
      hrational hr4 hr5 hwdvv hwsource hwboundary
  have hpull := CotangentCombination.pullback_vanishes A F N P K hK H G
    cotangentRelation L24Symmetry.stableArity n hterms hadded hz
  apply CotangentCombination.gwContraction_eq_zero A F N Omega P
    (cotangentRelation.pullback n) (L24Symmetry.stableArity.extraMarkings n) _ hpull
  intro t ht
  obtain ⟨z, hz, w, hw, rfl⟩ :=
    (CotangentCombination.mem_pullback cotangentRelation n t).mp ht
  exact hadded z hz w hw

end AxiomaticGW.L24Relation
