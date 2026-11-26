/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipandeGW
public import AxiomaticGW.Tautological.DecoratedGluingForgetful
public import AxiomaticGW.Tautological.DecoratedGluingMarkingBounds

/-!
# The full BP equation with arbitrary additional markings

The original twenty diagrams and all six marking assignments are retained.
The proved decorated forgetful expansion adds the rational-tail corrections
at both external and node cotangent flags. Its result pairs with arbitrary
upstairs ancestor powers and the full GW curve class.

Vanishing still follows from the accepted original BP certificate and its
original 3-spin source equations. The additional geometric inputs are the
one-psi comparison with its actual rational tail, primitive universal-curve
base change and the rational-tail section identity.
This is a family of reconstruction equations, not a termination theorem or
an unconditional geometric construction of the GW theory.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate GluingExpression PsiBoundaryExpansion

/-- The original component labels all have explicit finite equality decisions. -/
def paperLabelDecisions (i : Fin 20) : (paperTerm i).1.DecidableLabels :=
  match i with
  | ⟨0, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨1, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨2, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨3, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨4, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨5, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨6, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨7, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨8, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨9, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨10, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨11, _⟩ => by
    dsimp [paperTerm, paperExpression, GetzlerGraphs.join, GetzlerGraphs.close, DecidableLabels]
    exact ⟨inferInstance, inferInstance⟩
  | ⟨12, _⟩ => by
    dsimp [paperTerm, paperExpression, GetzlerGraphs.join, GetzlerGraphs.close, DecidableLabels]
    exact ⟨inferInstance, inferInstance⟩
  | ⟨13, _⟩ => by
    dsimp [paperTerm, paperExpression, GetzlerGraphs.join, GetzlerGraphs.close, DecidableLabels]
    exact ⟨inferInstance, inferInstance⟩
  | ⟨14, _⟩ => by
    dsimp [paperTerm, paperExpression, GetzlerGraphs.join, GetzlerGraphs.close, DecidableLabels]
    exact ⟨inferInstance, inferInstance⟩
  | ⟨15, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨16, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨17, _⟩ => by repeat' first | exact inferInstance | constructor
  | ⟨18, _⟩ => by
    dsimp [paperTerm, paperExpression, GetzlerGraphs.join, GetzlerGraphs.close, DecidableLabels]
    exact ⟨inferInstance, inferInstance⟩
  | ⟨19, _⟩ => by
    dsimp [paperTerm, paperExpression, GetzlerGraphs.join, GetzlerGraphs.close, DecidableLabels]
    exact ⟨inferInstance, inferInstance⟩
  | ⟨n + 20, h⟩ => False.elim (by omega)

/-- Bundle the existing paper term with its computational label decisions. -/
def paperCotangentTerm (i : Fin 20) : CotangentTerm 2 (Fin 3) :=
  ⟨(paperTerm i).1, (paperTerm i).2, paperLabelDecisions i⟩

/-- The same six original label assignments, with executable decorated pullback. -/
def orbitCotangentTerm (i : Fin 20) (e : Fin 6) : CotangentTerm 2 (Fin 3) :=
  (paperCotangentTerm i).relabel (labelPermutation e)

/-- The computational wrapper does not change the original published graph. -/
theorem orbitCotangentTerm_stratum (i : Fin 20) (e : Fin 6) :
    (orbitCotangentTerm i e).expression.decoratedStratum (orbitCotangentTerm i e).decoration =
      (paperStratum i).relabel (labelPermutation e) := orbitTerm_stratum i e

/-- All descendants of the sixteen lower-genus terms still have component genus at most one. -/
theorem added_term_lower_genus (i : Fin 20) (hi : 4 ≤ i.val) (e : Fin 6) (n : ℕ)
    (t : ℤ × CotangentTerm 2 (ExtraMarkings n (Fin 3)))
    (ht : t ∈ (orbitCotangentTerm i e).addMarkings n) :
    t.2.expression.maxComponentGenus ≤ 1 :=
  ((orbitCotangentTerm i e).addMarkings_bounds n t ht).2.trans (paperTerm_lower_genus i hi)

/-- Every term in every added-marking equation has codimension two. -/
theorem added_term_codimension (i : Fin 20) (e : Fin 6) (n : ℕ)
    (t : ℤ × CotangentTerm 2 (ExtraMarkings n (Fin 3)))
    (ht : t ∈ (orbitCotangentTerm i e).addMarkings n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 := by
  rw [((orbitCotangentTerm i e).addMarkings_bounds n t ht).1]
  change ((orbitCotangentTerm i e).expression.decoratedStratum
    (orbitCotangentTerm i e).decoration).codimension = 2
  rw [orbitCotangentTerm_stratum, TautologicalStratum.relabel_codimension,
    paperStratum_eq, columns_codimension]

universe u
attribute [local instance] strataRealizationModule

/-- Every added-marking BP equation is derived from the original source relations.
The effective class and all upstairs ancestor powers remain arbitrary. -/
theorem gw_forget_relation_from_generators {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    (p : Exchange) (hp : AcceptsExchange p)
    (hl : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hc : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    (n : ℕ) (hout : ∀ i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (beta : B) (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → V) :
    (∑ i, (paperCoefficient i * paperNormalization i) • ∑ e,
      (((orbitCotangentTerm i e).addMarkings n).map fun t ↦ t.1 •
        t.2.expression.gwDecoratedAncestorContraction Omega P I t.2.decoration beta k a).sum) =
      0 := by
  let w := P.monomial 2 (ExtraMarkings n (Fin 3)) (stableArity.extraMarkings n) k *
    Omega.omega 2 (ExtraMarkings n (Fin 3)) (stableArity.extraMarkings n) beta a
  let ev := (Z 2 (Fin 3)).integrateForgetExtra I stableArity n w
  have hz : ev paperRelation = 0 := by
    rw [StrataRealization.integrateForgetExtra_apply,
      realized_relation_from_generators Z F p hp hl hc hinterior hsource,
      map_zero, mul_zero, map_zero]
  have ht (i : Fin 20) (e : Fin 6) :
      ev (StrataModule.basis ((orbitTerm i e).1.decoratedStratum (orbitTerm i e).2)) =
      (((orbitCotangentTerm i e).addMarkings n).map fun t ↦ t.1 •
        t.2.expression.gwDecoratedAncestorContraction Omega P I t.2.decoration beta k a).sum := by
    change (Z 2 (Fin 3)).integrateForgetExtra I stableArity n w
      (StrataModule.basis ((orbitCotangentTerm i e).expression.decoratedStratum
        (orbitCotangentTerm i e).decoration)) = _
    rw [CotangentTerm.integrateForgetExtra_eq_sum Z F N P K hK H G
      (orbitCotangentTerm i e) n (hglue i e) (hcotangent i e) (hout i e) w]
    congr 1
    apply Multiset.map_congr rfl
    intro t hmem
    congr 1
    rw [← t.2.expression.gwDecoratedAncestorIntegral_apply Z Omega P I t.2.decoration
      beta k a]
    exact congrArg (fun f ↦ f a)
      (t.2.expression.gwDecoratedAncestorIntegral_eq_contraction Z F N Omega P
        t.2.decoration (hout i e t hmem).1 (hout i e t hmem).2 beta k)
  simpa only [paperRelation_as_terms, map_sum, map_smul, ht] using hz

end AxiomaticGW.BelorousskiPandharipande
