/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.GetzlerAncestors
import AxiomaticGW.Surfaces.CurveClasses
import AxiomaticGWTest.Tautological.GetzlerReplay

set_option linter.privateModule false

/-!
# Ancestor powers in marked Getzler contractions

Asymmetric powers detect incorrect component restrictions, misplaced node
labels, and reversed marking bijections. The final example consumes the frozen
Sage presentation in the full exceptional class with arbitrary powers. It is
a theorem under the stated geometric inputs, not a numerical surface model.
-/

namespace AxiomaticGWTest.Tautological.GetzlerAncestors

open AxiomaticGW GetzlerGraphs

private def powers : Fin 2 ⊕ Fin 1 → ℕ := Sum.elim ![2,5] ![3]

/-- The left node has power zero; both unequal external powers survive. -/
example : (PsiClasses.separatingLeftPowers powers) ∘ finSuccEquiv 2 = ![0,2,5] := by
  decide

/-- The right node has zero power independently of the right external power. -/
example : (PsiClasses.separatingRightPowers powers) ∘ finSuccEquiv 1 = ![0,3] := by
  decide

/-- Both self-gluing flags precede the retained external powers and receive zero. -/
example : (PsiClasses.nonseparatingPowers ![2,5,3]) ∘
    ((finSuccEquiv 4).trans (Equiv.optionCongr (finSuccEquiv 3))) = ![0,0,2,5,3] := by
  decide

/-- The elliptic/single/pair component order uses the covariant bijection,
so all four distinct powers move with their states. -/
example : (![2,3,5,7] : Fin 4 → ℕ) ∘ delta23Labels = ![7,5,2,3] := by decide

/-- The inverse bijection gives a different power assignment and is not interchangeable. -/
example : (![2,3,5,7] : Fin 4 → ℕ) ∘ delta23Labels.symm ≠ ![7,5,2,3] := by decide

section Theory

variable {R V B : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} (I : StableCurveIntegration C) (P : PsiClasses C)
  (Omega : GromovWittenTheory R V B D C)

/-- Relabelling the actual recursive expression transports powers and states
together, including when the input powers are asymmetric. -/
example (beta : B) (a : Fin 4 → V) :
    (delta23Expression.relabel (Equiv.swap 0 3)).gwAncestorContraction
      Omega P I beta ![2,3,5,7] a =
    delta23Expression.gwAncestorContraction Omega P I beta ![7,3,5,2]
      (a ∘ Equiv.swap 0 3) := by
  have hk : (![2,3,5,7] : Fin 4 → ℕ) ∘ Equiv.swap 0 3 = ![7,3,5,2] := by decide
  change delta23Expression.gwAncestorContraction Omega P I beta
    ((![2,3,5,7] : Fin 4 → ℕ) ∘ Equiv.swap 0 3) (a ∘ Equiv.swap 0 3) = _
  rw [hk]

/-- All 33 zero-power channels agree with the previously proved primary API,
without requiring a Getzler relation or any Gysin compatibility hypothesis. -/
example (beta : B) (a : Fin 4 → V) (i : Fin 33) :
    gwAncestorChannel Omega P I beta 0 a i = gwChannel Omega I beta a i :=
  gwAncestorChannel_zero Omega P I beta a i

end Theory

/-- The actual decoded certificate gives the equation with arbitrary powers
and the full E₁+E₂ class, under the same primitive realization data. -/
example {R V : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {C : StableCurveCohomology R} (I : StableCurveIntegration C) (P : PsiClasses C)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (hcompat : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory R V SurfaceTarget.blowupTwo.Curve
      SurfaceTarget.blowupTwo.effective C) (k : Fin 4 → ℕ) (a : Fin 4 → V) :
    (∑ i, algebraMap ℚ R (requested i) * gwAncestorChannel Omega P I ![1,1,0] k a i) = 0 :=
  exchange_ancestor_eq_zero A F N hcompat G hcycle Omega P ![1,1,0] k a
    GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Tautological.GetzlerAncestors
