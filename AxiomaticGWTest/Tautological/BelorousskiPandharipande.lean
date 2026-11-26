/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.BelorousskiPandharipandeGW
import AxiomaticGW.Tautological.Fixtures.BelorousskiPandharipandeReplay

/-!
# Published BP normalization, source provenance and geometric consumer regressions

The tests distinguish a six-assignment sum from an orbit average, check the
elliptic-tail exchange factor and the three specified genus-two cotangent
placements, and consume the actual incoming certificate with original
geometric generator hypotheses. No numerical genus-two value is postulated.
-/

open AxiomaticGW RelationCertificate BelorousskiPandharipande

example : AcceptsExchange BelorousskiPandharipandeReplay.exchange :=
  BelorousskiPandharipandeReplay.accepted

example : (Finset.univ.filter fun i ↦ requested i ≠ 0).card = 46 := by decide +kernel

example : requested 12 = 6 ∧ requested 13 = -6 ∧ requested 26 = 12 ∧ requested 27 = -4 := by
  decide +kernel

example : requested 69 = 6 / 5 ∧ requested 90 = 3 / 5 := by decide +kernel

example : paperNormalization 4 = 1 / 2 ∧ paperNormalization 7 = 1 ∧
    paperNormalization 15 = 1 / 2 := by decide +kernel

example : paperCoefficient 0 = -2 ∧ paperCoefficient 11 = 1 / 60 ∧
    paperCoefficient 19 = -1 / 10 := by decide +kernel

example : (paperGraph 1).halfEdgePsiPower ⟨0, by decide +kernel⟩ 0 = 1 ∧
    (paperGraph 1).halfEdgePsiPower ⟨0, by decide +kernel⟩ 1 = 0 := by
  decide +kernel

example : (paperGraph 2).legPsiPower 0 = 1 ∧ (paperGraph 3).legPsiPower 0 = 0 ∧
    (paperGraph 3).halfEdgePsiPower ⟨0, by decide +kernel⟩ 0 = 1 := by decide +kernel

example : sourceRow 5 = GenusOnePsi.rows 0 ∧ sourceRow 6 = GenusOnePsi.rows 1 := ⟨rfl, rfl⟩

example : sourceMap 3 (StrataModule.basis (GenusOnePsi.columns 0)) =
    StrataModule.basis (columns 73) := by
  have h := sourceMap_columns 3 ⟨0, by decide +kernel⟩
  have hd : sourceDestinations 3 ⟨0, by decide +kernel⟩ = 73 := by decide +kernel
  rw [elliptic_source_columns, hd] at h
  exact h

example : sourceMap 5 (StrataModule.basis (sourceColumns 5 ⟨4, by decide +kernel⟩)) =
    StrataModule.basis (columns 92) := by
  have h := sourceMap_columns 5 ⟨4, by decide +kernel⟩
  have hd : sourceDestinations 5 ⟨4, by decide +kernel⟩ = 92 := by decide +kernel
  rw [hd] at h
  exact h

example : interpret columns requested ≠ 0 := requested_ne_zero

example : toPushforward (toMonomial (Pi.single 1 7)) = Pi.single 1 7 :=
  (conversion_inverse _).1

example : ∀ i, 4 ≤ i.val → (paperTerm i).1.maxComponentGenus ≤ 1 := paperTerm_lower_genus

universe u
attribute [local instance] strataRealizationModule

example {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (hl : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hc : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    (beta : B) (k : Fin 3 → ℕ) (a : Fin 3 → V) :
    (∑ i, (paperCoefficient i * paperNormalization i) •
      ∑ e, (orbitTerm i e).1.gwDecoratedAncestorContraction Omega P I (orbitTerm i e).2
        beta k a) = 0 :=
  gw_relation_from_generators Z F N Omega P BelorousskiPandharipandeReplay.exchange
    BelorousskiPandharipandeReplay.accepted hl hc hinterior hsource hglue hcotangent beta k a
