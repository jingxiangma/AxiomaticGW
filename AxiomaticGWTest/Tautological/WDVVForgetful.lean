/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.WDVVForgetful
import AxiomaticGWTest.Tautological.WDVVReplay

set_option linter.privateModule false

namespace AxiomaticGWTest.Tautological.WDVVForgetful

open AxiomaticGW

/-- Both placements preserve every original label of the nontrivial second channel. -/
example : (((WDVV.expression 1).addMarkings 1).map fun z ↦
    fun i : Fin 4 ↦ (z.graph.graph.legVertex (some i)).val) =
    [![0, 1, 0, 1], ![0, 1, 0, 1]] := by decide +kernel

/-- Two ordered markings retain all four assignments, including different orders. -/
example : (((WDVV.expression 2).addMarkings 2).map fun z ↦
    ((z.graph.graph.legVertex none).val, (z.graph.graph.legVertex (some none)).val)) =
    [(0, 0), (1, 0), (0, 1), (1, 1)] := by decide +kernel

/-- The original incoming certificate supports arbitrary markings and powers. -/
example {R V B : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B} {C : StableCurveCohomology R}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S) (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V) :
    (∑ i, algebraMap ℚ R (WDVV.requested i) *
      WDVV.gwAncestorChannelWithMarkings Omega P I n beta k a i) = 0 :=
  WDVV.exchange_ancestor_with_markings_eq_zero A F N hsource H hboundary Omega P n houtput
    beta k a WDVVReplay.presentation WDVVReplay.accepted

end AxiomaticGWTest.Tautological.WDVVForgetful
