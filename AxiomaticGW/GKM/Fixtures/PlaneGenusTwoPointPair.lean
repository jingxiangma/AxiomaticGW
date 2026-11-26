/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsLowPsi
public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiTwo

/-!
# A certified nonzero two-point genus-two plane descendant

The complete product equation gives the ancestor value as `29/2880` plus
three times the existing degree-zero hyperplane terminal `-1/960`.
The descendant comparison adds twice the degree-zero ancestor with a unit
and a first descendant of a point; that terminal is zero. Thus the original
plane descendant algorithm returns `1/144` for the full incoming GKM query.

The boundary terms, terminal values and comparison are checked separately.
The geometric interpretation is the existing plane query theorem with its
original geometric hypotheses and three finite seeds. This fixture does not
certify the producer's equivariant localization or import CohFT classes.
-/

@[expose] public section

namespace AxiomaticGW.GKM.PlaneGenusTwoPointPair
open BelorousskiPandharipande SurfaceGenusTwo PlaneGenusTwoAncestors

/-- The complete two-point request in the plane line class. -/
def query : SurfaceQuery .plane := ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩

/-- Exactly the three ancestor keys needed by this descendant calculation. -/
def queries : Finset (SurfaceAncestorKey .plane) := {key 2, key 3, key 11}

/-- The original product equation and both terminal equations close this small table. -/
theorem ancestors_accepted :
    checkAncestorValues (planeLowPsiValueWith GenusTwoPlaneLine.values)
      queries values = true := by
  rw [checkAncestorValues, decide_eq_true_eq]
  intro q hq
  simp only [queries, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · rw [checkAncestorRow, decide_eq_true_eq]
    refine ⟨by decide +kernel, ?_⟩
    rw [dif_pos (show (key 2).totalPsi ≤ 1 by decide +kernel), values_key]
    exact LowPsi.terminal_2
  · rw [checkAncestorRow, decide_eq_true_eq]
    refine ⟨by decide +kernel, ?_⟩
    rw [dif_pos (show (key 3).totalPsi ≤ 1 by decide +kernel), values_key]
    exact LowPsi.terminal_3
  · rw [checkAncestorRow, decide_eq_true_eq]
    refine ⟨by decide +kernel, ?_⟩
    rw [dif_neg (show ¬(key 11).totalPsi ≤ 1 by decide +kernel)]
    unfold ancestorStep
    rw [PsiTwo.reduction_11]
    decide +kernel

/-- Collecting all ten original boundary terms retains their lone genus-two variable. -/
theorem reduction_sum (v : SurfaceAncestorKey .plane → ℚ) :
    RationalTerms.eval v (terms 11) = 29 / 2880 + 3 * v (key 2) := by
  change RationalTerms.eval v terms_11 = _
  norm_num [RationalTerms.eval, terms_11]
  ring

/-- The terminating ancestor algorithm satisfies this complete product equation. -/
theorem ancestor_equation :
    planeAncestorValueWith GenusTwoPlaneLine.values (key 11) =
      29 / 2880 + 3 * planeAncestorValueWith GenusTwoPlaneLine.values (key 2) := by
  change ancestorValue (planeLowPsiValueWith GenusTwoPlaneLine.values) (key 11) = _
  rw [ancestorValue_step _ _ (by decide +kernel) (by decide +kernel),
    ancestorStep, PsiTwo.reduction_11]
  exact reduction_sum _

/-- The held low-psi hyperplane value is reused, without a new seed. -/
theorem hyperplane_terminal :
    planeAncestorValueWith GenusTwoPlaneLine.values (key 2) = -1 / 960 := by
  rw [planeAncestorValueWith, ancestorValue_low _ _ (by decide +kernel) (by decide +kernel)]
  exact LowPsi.terminal_2.symm

/-- The unit/point terminal in the descendant correction is zero. -/
theorem correction_terminal :
    planeAncestorValueWith GenusTwoPlaneLine.values (key 3) = 0 := by
  rw [planeAncestorValueWith, ancestorValue_low _ _ (by decide +kernel) (by decide +kernel)]
  exact LowPsi.terminal_3.symm

/-- The original comparison at this exact ordered request, before ancestor evaluation. -/
def descendantTerms : RationalTerms (SurfaceAncestorKey .plane) :=
  SurfaceDescendant.mixedAncestorTerms 2 (Fin query.insertions.length)
    (by simp only [StableArity, Fintype.card_fin]; omega)
    (List.finRange query.insertions.length) query.beta
    (fun i ↦ (query.insertions.get i).psi) 0 (fun i ↦ (query.insertions.get i).label)

/-- Both marking occurrences contribute the same zero-class correction. -/
theorem descendant_terms :
    descendantTerms = {(1, {key 3}), (1, {key 3}), (1, {key 11})} := by
  decide +kernel

/-- The complete descendant comparison retains the ancestor and both tail terms. -/
theorem descendant_equation :
    planeQueryValueWith? GenusTwoPlaneLine.values query =
      some (planeAncestorValueWith GenusTwoPlaneLine.values (key 11) +
        2 * planeAncestorValueWith GenusTwoPlaneLine.values (key 3)) := by
  change some (RationalTerms.eval (planeAncestorValueWith GenusTwoPlaneLine.values)
    descendantTerms) = _
  rw [descendant_terms]
  congr 1
  norm_num [RationalTerms.eval]
  ring

/-- Exact-query kernel certificate against the original descendant reconstruction. -/
theorem accepted : planeQueryValue? query = some (1 / 144) := by
  rw [← planeQueryValueWith?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted
    query (by decide +kernel), descendant_equation, ancestor_equation,
    hyperplane_terminal, correction_terminal]
  norm_num

/-- The named request matches the held GKM request with every insertion retained. -/
theorem gkm_query : query = PlaneGenusTwoFewMarkingsReplay.requests 46 := by decide +kernel

/-- The imported rational value is compared only after the original algorithm is checked. -/
theorem gkm_accepted :
    planeQueryValue? (PlaneGenusTwoFewMarkingsReplay.requests 46) =
      some (PlaneGenusTwoFewMarkingsReplay.values 46) := by
  rw [← gkm_query]
  exact accepted

end AxiomaticGW.GKM.PlaneGenusTwoPointPair
