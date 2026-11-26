/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.GetzlerForgetful
import AxiomaticGW.Surfaces.CurveClasses
import AxiomaticGWTest.Tautological.GetzlerReplay

set_option linter.privateModule false

/-!
# Additional-marking incidence, multiplicity, and replay regressions

The incidence checks inspect the actual finite graphs, separately from the
recursive cohomology argument. They cover all 33 original columns and both
marking orders. A symmetric graph checks that equal strata retain coefficient
two. The final consumer keeps arbitrary ancestor powers and the full E1+E2
class. None of these examples supplies a numerical surface GW model.
-/

namespace AxiomaticGWTest.Tautological.GetzlerForgetful

open AxiomaticGW GetzlerGraphs

/-- Sage's one-marking count agrees with the general kernel theorem. -/
example : (∑ i : Fin 33, ((expression i).addMarkings 1).length) = 91 := by
  rw [sum_length_addMarkings]
  norm_num

/-- Two ordered extra markings retain all 257 placements. -/
example : (∑ i : Fin 33, ((expression i).addMarkings 2).length) = 257 := by
  rw [sum_length_addMarkings]
  norm_num

/-- Each old vertex receives the new label exactly once, in every graph family. -/
example (i : Fin 33) :
    ((expression i).addMarking.map fun z ↦ (z.graph.graph.legVertex none).val) =
      List.range (expression i).graph.graph.vertexCount := by
  fin_cases i <;> decide

/-- Both ordered markings range independently over the old vertex set. -/
example (i : Fin 33) :
    (((expression i).addMarkings 2).map fun z ↦
      ((z.graph.graph.legVertex (some none)).val, (z.graph.graph.legVertex none).val)) =
      (List.range (expression i).graph.graph.vertexCount).flatMap fun v ↦
        (List.range (expression i).graph.graph.vertexCount).map fun w ↦ (v, w) := by
  fin_cases i <;> decide

/-- Record genera and all ordered node incidences, independently of external labels. -/
private def internalData {S : Type} [Fintype S] (G : DecoratedStableGraph S) :
    List ℕ × List (ℕ × ℕ) :=
  (List.ofFn G.graph.genus, List.ofFn fun e ↦
    ((G.graph.endpoint e 0).val, (G.graph.endpoint e 1).val))

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all 91 actual graphs, including their full node incidences.
/-- No existing external marking or node is consumed by the new marking. -/
example (i : Fin 33) : ((expression i).addMarking.all fun z ↦ decide
    (internalData z.graph = internalData (expression i).graph ∧
      (List.ofFn fun s : Fin 4 ↦ (z.graph.graph.legVertex (some s)).val) =
        List.ofFn (fun s : Fin 4 ↦ ((expression i).graph.graph.legVertex s).val))) = true := by
  fin_cases i <;> decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks all 257 actual graphs, including their full node incidences.
/-- After two additions, the original four labels and all nodes still agree. -/
example (i : Fin 33) : (((expression i).addMarkings 2).all fun z ↦ decide
    (internalData z.graph = internalData (expression i).graph ∧
      (List.ofFn fun s : Fin 4 ↦ (z.graph.graph.legVertex (some (some s))).val) =
        List.ofFn (fun s : Fin 4 ↦ ((expression i).graph.graph.legVertex s).val))) = true := by
  fin_cases i <;> decide

private def symmetric : GluingExpression 2 (Fin 0 ⊕ Fin 0) :=
  (GluingExpression.fundamental 1 (Option (Fin 0)) (by norm_num [StableArity])).separating
    (.fundamental 1 (Option (Fin 0)) (by norm_num [StableArity]))

private def symmetricLeft := symmetric.addMarking[0]'(by decide)
private def symmetricRight := symmetric.addMarking[1]'(by decide)

private theorem symmetric_eq : symmetricRight.stratum = symmetricLeft.stratum := by
  apply Quotient.sound
  apply (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
  decide

/-- Vertex symmetry combines the two placements with multiplicity two. -/
example : (symmetric.addMarking.map fun z ↦ StrataModule.basis z.stratum).sum =
    (2 : ℚ) • StrataModule.basis symmetricLeft.stratum := by
  have hl : symmetric.addMarking = [symmetricLeft, symmetricRight] := rfl
  rw [hl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    symmetric_eq, two_smul]

private def parallelSource : GluingExpression 0 (Option (Option (Fin 4))) :=
  ((join (m := 3) (n := 3) 0 0
    (.fundamental 0 (Fin 4) (by norm_num [StableArity]))
    (.fundamental 0 (Fin 4) (by norm_num [StableArity]))).relabel (Equiv.swap 1 3)).relabel
      ((finSuccEquiv 5).trans (Equiv.optionCongr (finSuccEquiv 4)))

private def placedSource := parallelSource.addMarking[1]'(by decide)

/-- Reversing the required node permutation gives a loop, not parallel edges. -/
example :
    ((placedSource.relabel (forgetNonseparatingEquiv (Fin 4))).nonseparating.graph).isomorphic?
      ((placedSource.relabel (forgetNonseparatingEquiv (Fin 4)).symm).nonseparating.graph) =
        false := by decide

/-- Canonical finite-label inference works for an arbitrary number of additions. -/
example (n : ℕ) : Fintype.card (ExtraMarkings n (Fin 4)) = n + 4 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Option (ExtraMarkings n (Fin 4))) = n + 1 + 4
    rw [Fintype.card_option, ih]

/-- Zero-based exchange labels retain the four old markings and append the new ones. -/
example :
    (ExtraMarkings.finEquiv 2 4 none = 5) ∧
      (ExtraMarkings.finEquiv 2 4 (some none) = 4) ∧
      (∀ i : Fin 4, (ExtraMarkings.finEquiv 2 4 (some (some i))).val = i.val) := by decide

/-- The actual decoded certificate gives the equation with any number of
additional markings and powers, while keeping both exceptional coordinates. -/
example {R V : Type} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {C : StableCurveCohomology R} (I : StableCurveIntegration C) (P : PsiClasses C)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory R V SurfaceTarget.blowupTwo.Curve
      SurfaceTarget.blowupTwo.effective C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V) :
    (∑ i, algebraMap ℚ R (requested i) *
      gwAncestorChannelWithMarkings Omega P I n ![1,1,0] k a i) = 0 :=
  exchange_ancestor_with_markings_eq_zero A F N H hsource G hcycle Omega P n houtput ![1,1,0]
    k a GetzlerReplay.presentation GetzlerReplay.accepted

end AxiomaticGWTest.Tautological.GetzlerForgetful
