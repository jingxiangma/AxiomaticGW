/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupRecursion

/-!
# Energy bounds for actual blowup reconstruction dependencies

The original H and N equations use source class beta+Ei. Their source-class
canonical columns cancel, so every nonzero canonical coefficient has energy
at most that of beta. The H cancellation uses positive target energy; the
N cancellation is unconditional. The unshifted P and K rows retain their
original effective-subclass bound.

The uniform result applies to every positive-plane-degree row actually used
by the recursion. It concerns canonical genus-two variables after genuine
coefficient cancellation. Lower-genus scalar constants may still use source
energy energy(beta)+1. An energy bound does not replace exact full-class and
exceptional-label dependency coverage, or the strictly earlier order proof.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupDependencyEnergy
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder

variable {X : SurfaceTarget}
set_option maxRecDepth 20000

private theorem energy_le_of_proper_shifted_subclass (i : Fin X.blowups)
    (beta gamma delta : X.Curve) (hs : gamma + delta = beta + X.exceptionalCurve i)
    (hg : gamma ≠ beta + X.exceptionalCurve i) :
    X.effective.energy gamma ≤ X.effective.energy beta := by
  have hz : delta ≠ 0 := by
    intro h
    rw [h, add_zero] at hs
    exact hg hs
  have hp : 0 < X.effective.energy delta := Nat.pos_of_ne_zero
    (fun h ↦ hz ((X.effective.energy_eq_zero_iff delta).mp h))
  have he := congrArg X.effective.energy hs
  rw [map_add, X.energy_add_exceptionalCurve] at he
  omega

/-- Every canonical source-class coefficient cancels in the original N combination. -/
theorem n_source_canonical_coefficient_eq_zero (i : Fin X.blowups)
    (beta : X.Curve) (family : Family X) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {.inr (family.query (beta + X.exceptionalCurve i))} = 0 := by
  cases family with
  | primary =>
    exact SurfaceGenusTwoBlowupNSourcePrimary.row_source_primary_eq_zero i beta _
  | hyperplane =>
    exact SurfaceGenusTwoBlowupNCoefficients.row_source_nonprimary_coefficient_eq_zero
      i beta _ (fun eta m ↦ SurfaceFirstDescendant.query_ne_points _ eta .hyperplane _ m) rfl
  | point =>
    exact SurfaceGenusTwoBlowupNCoefficients.row_source_nonprimary_coefficient_eq_zero
      i beta _ (fun eta m ↦ SurfaceFirstDescendant.query_ne_points _ eta .point _ m) rfl
  | exceptional j =>
    exact SurfaceGenusTwoBlowupNCoefficients.row_source_nonprimary_coefficient_eq_zero
      i beta _
      (fun eta m ↦ SurfaceFirstDescendant.query_ne_points _ eta (.exceptional j) _ m) rfl

/-- Source cancellation improves the N source-energy bound by one, for every full class. -/
theorem n_coefficient_energy_le (i : Fin X.blowups) (beta gamma : X.Curve)
    (family : Family X)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupNRelation.row X i beta)
      {.inr (family.query gamma)} ≠ 0) :
    X.effective.energy gamma ≤ X.effective.energy beta := by
  obtain ⟨delta, hs⟩ := SurfaceGenusTwoBlowupNRelation.canonical_coefficient_subclass
    i beta gamma family hc
  apply energy_le_of_proper_shifted_subclass i beta gamma delta hs
  intro hg
  rw [hg] at hc
  exact hc (n_source_canonical_coefficient_eq_zero i beta family)

/-- All canonical source-class columns of the H row vanish at positive target energy. -/
theorem h_source_canonical_coefficient_eq_zero (i : Fin X.blowups)
    (beta : X.Curve) (family : Family X) (hbeta : 0 < X.effective.energy beta) :
    RationalTerms.coefficient (SurfaceGenusTwoBlowupHPivots.row X i beta)
      {.inr (family.query (beta + X.exceptionalCurve i))} = 0 := by
  have hd : X.planeDegree (beta + X.exceptionalCurve i) = X.planeDegree beta := by
    rw [map_add, X.planeDegree_exceptionalCurve, add_zero]
  cases family with
  | hyperplane =>
    exact SurfaceGenusTwoBlowupHSupport.source_column_row_coefficient_eq_zero X i beta hbeta
  | primary =>
    exact SurfaceGenusTwoBlowupHOtherFamilies.primary_row_coefficient_eq_zero_of_same_planeDegree
      X i beta _ _ hd
  | point =>
    exact
      SurfaceGenusTwoBlowupHOtherFamilies.first_other_row_coefficient_eq_zero_of_same_planeDegree
        X i beta _ .point _ (by intro h; cases h) hd
  | exceptional j =>
    exact
      SurfaceGenusTwoBlowupHOtherFamilies.first_other_row_coefficient_eq_zero_of_same_planeDegree
        X i beta _ (.exceptional j) _ (by intro h; cases h) hd

/-- The complete original shifted H row needs no canonical class above the target energy. -/
theorem h_coefficient_energy_le (i : Fin X.blowups) (beta gamma : X.Curve)
    (family : Family X) (hbeta : 0 < X.effective.energy beta)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupHPivots.row X i beta)
      {.inr (family.query gamma)} ≠ 0) :
    X.effective.energy gamma ≤ X.effective.energy beta := by
  have hle : gamma ≤ beta + X.exceptionalCurve i := by
    by_contra hn
    have hb := L24Relation.genusTwoTerms_bound X
      (SurfaceGenusTwoBlowupHPivots.pointCount X beta)
      (SurfaceGenusTwoBlowupHPivots.sourceCurve X i beta) 0
      (SurfaceGenusZero.pointLabels (SurfaceGenusTwoBlowupHPivots.labels X i)
        (SurfaceGenusTwoBlowupHPivots.pointCount X beta))
    have hv : SurfaceGenusZero.variableCurve (.inr (family.query gamma)) = gamma := by
      cases family <;> rfl
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl
      (.inr (family.query gamma)) (by rwa [hv]))
  have hs : gamma + (beta + X.exceptionalCurve i - gamma) = beta + X.exceptionalCurve i := by
    funext k
    exact Nat.add_sub_of_le (hle k)
  apply energy_le_of_proper_shifted_subclass i beta gamma _ hs
  intro hg
  rw [hg] at hc
  exact hc (h_source_canonical_coefficient_eq_zero i beta family hbeta)

/-- Unshifted original BP rows retain their ordinary full-class energy bound. -/
theorem bp_coefficient_energy_le (n : ℕ) (beta gamma : X.Curve)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) (family : Family X)
    (hc : RationalTerms.coefficient
      (BelorousskiPandharipande.normalizedGenusTwoTerms X n beta 0 a)
      {.inr (family.query gamma)} ≠ 0) :
    X.effective.energy gamma ≤ X.effective.energy beta := by
  have hle : gamma ≤ beta := by
    by_contra hn
    have hb := BelorousskiPandharipande.genusTwoTerms_bound X n beta 0 a
    have hv : SurfaceGenusZero.variableCurve (.inr (family.query gamma)) = gamma := by
      cases family <;> rfl
    exact hc (hb.normalized_coefficient_eq_zero_of_not_le le_rfl
      (.inr (family.query gamma)) (by rwa [hv]))
  have hs : gamma + (beta - gamma) = beta := by
    funext k
    exact Nat.add_sub_of_le (hle k)
  have he := congrArg X.effective.energy hs
  rw [map_add] at he
  omega

/-- Uniform canonical coefficient energy bound for the actual H/P/N/K dispatch.
The positivity premise is used only by the source-H cancellation lemma. -/
theorem dependency_energy_le (i : Fin X.blowups) (s t : State X)
    (hs : 0 < X.effective.energy s.1)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s)
      {.inr (t.2.query t.1)} ≠ 0) :
    X.effective.energy t.1 ≤ X.effective.energy s.1 := by
  obtain ⟨beta, f⟩ := s
  obtain ⟨gamma, family⟩ := t
  cases f with
  | hyperplane => exact h_coefficient_energy_le i beta gamma family hs hc
  | primary => exact n_coefficient_energy_le i beta gamma family hc
  | point => exact bp_coefficient_energy_le _ beta gamma _ family hc
  | exceptional j => exact bp_coefficient_energy_le _ beta gamma _ family hc

/-- Every row actually used by the recursive algorithm has positive plane degree,
so all its surviving canonical dependencies are within the target energy bound. -/
theorem dependency_energy_le_of_positive_planeDegree (i : Fin X.blowups) (s t : State X)
    (hs : 0 < X.planeDegree s.1)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s)
      {.inr (t.2.query t.1)} ≠ 0) :
    X.effective.energy t.1 ≤ X.effective.energy s.1 := by
  apply dependency_energy_le i s t _ hc
  apply Nat.pos_of_ne_zero
  intro h
  have hz := (X.effective.energy_eq_zero_iff s.1).mp h
  rw [hz, map_zero] at hs
  omega

end AxiomaticGW.SurfaceGenusTwoBlowupDependencyEnergy
