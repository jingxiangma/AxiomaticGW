/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoUnitPairClaims
public import AxiomaticGW.GKM.Fixtures.GenusTwoOneMarkingReplay
public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineOneMarkingReplay
public import AxiomaticGW.Surfaces.GenusTwoBlowupUnitPairs
public import AxiomaticGW.Surfaces.GenusTwoFewMarkings

/-! # Ordinary localization comparisons for 76 ordered two-marked unit requests

Each comparison checks the ordered query, the full class and power of the recognized
singleton, and its exact reconstructed value. Agreement of the unit reduction with the
unmodified blowup evaluator uses its original reconstruction theorem and string/dilaton laws.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoUnitPairs
open SurfaceGenusTwo

private def binding {X : SurfaceTarget} (q : SurfaceQuery X) : Option (SurfaceQuery X × ℚ) :=
  (unitPairReduction? q).map (fun (rule, s) ↦ (⟨2, q.beta, [s]⟩, rule.factor))

private def factor : Fin 4 → ℚ := ![1, 1, 3, 3]

private theorem compare {X : SurfaceTarget} (i : Fin X.blowups) (q singleton : SurfaceQuery X)
    (c v : ℚ) (hb : binding q = some (singleton, c))
    (hs : SurfaceGenusTwoBlowupDescendants.queryValue? i singleton = some v) :
    unitPairValue? i q = some (c * v) := by
  unfold binding at hb
  cases hr : unitPairReduction? q with
  | none => simp only [hr, Option.map_none, reduceCtorEq] at hb
  | some p =>
    obtain ⟨r, s⟩ := p
    simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [unitPairValue?, hr]
    change (SurfaceGenusTwoBlowupDescendants.queryValue? i _).map _ = _
    rw [hs]
    rfl

/-- All 16 ordered F₁ exceptional-class queries lie in the prescribed benchmark and agree. -/
theorem OneBlowup.accepted (j : Fin 4) (k : Fin 4) :
    FewMarkingQuery (OneBlowup.requests j k) ∧
    unitPairValue? 0 (OneBlowup.requests j k) = some (OneBlowup.values j k) := by
  refine ⟨?_, ?_⟩
  · revert j k; unfold FewMarkingQuery; decide +kernel
  · have hb : binding (OneBlowup.requests j k) =
        some (GenusTwoOneMarking.OneBlowup.requests j, factor k) := by
      revert j k; decide +kernel
    have hv : factor k * GenusTwoOneMarking.OneBlowup.values j = OneBlowup.values j k := by
      revert j k; decide +kernel
    exact (compare 0 _ _ _ _ hb (GenusTwoOneMarking.OneBlowup.accepted j)).trans (congrArg some hv)

/-- All 40 requests at the two exceptional curves keep their individual divisor and curve labels. -/
theorem TwoBlowups.accepted (j : Fin 10) (k : Fin 4) :
    FewMarkingQuery (TwoBlowups.requests j k) ∧
    unitPairValue? 0 (TwoBlowups.requests j k) = some (TwoBlowups.values j k) := by
  refine ⟨?_, ?_⟩
  · revert j k; unfold FewMarkingQuery; decide +kernel
  · have hb : binding (TwoBlowups.requests j k) =
        some (GenusTwoOneMarking.TwoBlowups.requests j, factor k) := by
      revert j k; decide +kernel
    have hv : factor k * GenusTwoOneMarking.TwoBlowups.values j = TwoBlowups.values j k := by
      revert j k; decide +kernel
    exact (compare 0 _ _ _ _ hb (GenusTwoOneMarking.TwoBlowups.accepted j)).trans (congrArg some hv)

/-- All 16 requests on L extend the four certified high-power strict-line singletons. -/
theorem StrictLine.accepted (j : Fin 4) (k : Fin 4) :
    FewMarkingQuery (StrictLine.requests j k) ∧
    unitPairValue? 0 (StrictLine.requests j k) = some (StrictLine.values j k) := by
  refine ⟨?_, ?_⟩
  · revert j k; unfold FewMarkingQuery; decide +kernel
  · have hb : binding (StrictLine.requests j k) =
        some (BlowupTwoLineOneMarkingReplay.requests j.castSucc, factor k) := by
      revert j k; decide +kernel
    have hv : factor k * BlowupTwoLineOneMarkingReplay.values j.castSucc = StrictLine.values j k :=
      by revert j k; decide +kernel
    exact (compare 0 _ _ _ _ hb (BlowupTwoLineOneMarkingReplay.high_accepted j)).trans
      (congrArg some hv)

/-- The four remaining native strict-line rows reduce to the fifth singleton. -/
theorem StrictLinePoint.accepted_of_point
    (hs : SurfaceGenusTwoBlowupDescendants.queryValue? 0
      (BlowupTwoLineOneMarkingReplay.requests 4) = some (BlowupTwoLineOneMarkingReplay.values 4))
    (j : Fin 1) (k : Fin 4) :
    FewMarkingQuery (StrictLinePoint.requests j k) ∧
      unitPairValue? 0 (StrictLinePoint.requests j k) = some (StrictLinePoint.values j k) := by
  refine ⟨?_, ?_⟩
  · revert j k; unfold FewMarkingQuery; decide +kernel
  · have hb : binding (StrictLinePoint.requests j k) =
        some (BlowupTwoLineOneMarkingReplay.requests 4, factor k) := by
      revert j k; decide +kernel
    have hv : factor k * BlowupTwoLineOneMarkingReplay.values 4 = StrictLinePoint.values j k := by
      revert j k; decide +kernel
    exact (compare 0 _ _ _ _ hb hs).trans (congrArg some hv)

end AxiomaticGW.GKM.GenusTwoUnitPairs
