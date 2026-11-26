/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.BelorousskiPandharipandeForgetful
import AxiomaticGW.Tautological.Fixtures.BelorousskiPandharipandeReplay

-- This regression module intentionally contains only private examples.
set_option linter.privateModule false

/-!
# Cotangent pullback signs, flag placement and the complete BP consumer

These regressions inspect actual graph data with kernel reduction. In
particular, a psi-square correction has coefficient minus one, with the
remaining power at the main node and no power on the three-point tail.
-/

open AxiomaticGW GluingExpression BelorousskiPandharipande PsiBoundaryExpansion

private def square : CotangentTerm 2 (Fin 1) :=
  CotangentTerm.fundamental 2 (Fin 1) (by norm_num [StableArity]) (fun _ ↦ 2)

private def signature {n : ℕ} (G : DecoratedStableGraph (Fin n)) : List (List ℕ) :=
  [List.ofFn G.graph.genus, List.ofFn (fun i ↦ (G.graph.legVertex i).val),
    List.ofFn G.legPsiPower,
    (List.ofFn fun e ↦ [(G.graph.endpoint e 0).val, (G.graph.endpoint e 1).val]).flatten,
    (List.ofFn fun e ↦ [G.halfEdgePsiPower e 0, G.halfEdgePsiPower e 1]).flatten]

example : (square.addMarking.map fun t ↦ (t.1,
    signature ((t.2.expression.decoratedGraph t.2.decoration).relabel
      (ExtraMarkings.finEquiv 1 1)))) =
    {(1, [[2], [0, 0], [2, 0], [], []]),
     (-1, [[2, 0], [1, 1], [0, 0], [0, 1], [1, 0]])} := by decide +kernel

example : (square.addMarking.map Prod.fst) ≠ ({1, -2} : Multiset ℤ) := by decide +kernel

example : (CotangentTerm.fundamental 2 (Fin 1) (by norm_num [StableArity])
    (fun _ ↦ 0)).addMarking.card = 1 := by decide +kernel

example : (CotangentTerm.fundamental 2 (Fin 0) (by norm_num [StableArity])
    Fin.elim0).addMarking.card = 1 := by decide +kernel

example (i : Fin 20) :
    ((paperCotangentTerm i).addMarking.map Prod.fst).count (-1) =
      if i = 1 ∨ i = 2 ∨ i = 3 then 1 else 0 := by
  fin_cases i <;> decide +kernel

example (i : Fin 20) (e : Fin 6) (n : ℕ)
    (t : ℤ × CotangentTerm 2 (ExtraMarkings n (Fin 3)))
    (ht : t ∈ (orbitCotangentTerm i e).addMarkings n) :
    (t.2.expression.decoratedGraph t.2.decoration).codimension = 2 :=
  added_term_codimension i e n t ht

example (i : Fin 20) (hi : 4 ≤ i.val) (e : Fin 6) (n : ℕ)
    (t : ℤ × CotangentTerm 2 (ExtraMarkings n (Fin 3)))
    (ht : t ∈ (orbitCotangentTerm i e).addMarkings n) :
    t.2.expression.maxComponentGenus ≤ 1 := added_term_lower_genus i hi e n t ht

universe u
attribute [local instance] strataRealizationModule

example {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    (hl : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hc : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (RelationCertificate.interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    (n : ℕ) (hout : ∀ i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (beta : B) (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → V) :
    (∑ i, (paperCoefficient i * paperNormalization i) • ∑ e,
      (((orbitCotangentTerm i e).addMarkings n).map fun t ↦ t.1 •
        t.2.expression.gwDecoratedAncestorContraction Omega P I t.2.decoration beta k a).sum) = 0 :=
  gw_forget_relation_from_generators Z F N Omega P K hK H G
    BelorousskiPandharipandeReplay.exchange BelorousskiPandharipandeReplay.accepted
    hl hc hinterior hsource hglue hcotangent n hout beta k a
