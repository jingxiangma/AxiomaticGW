/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalComparison
public import AxiomaticGW.GKM.Fixtures.BlowupTwoDoubleExceptionalSingletons
public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Original Bl₂ reconstruction within the full 210-row native exceptional comparison -/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoDoubleExceptionalFewMarkings
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

private theorem singletons (j : Fin 10) :
    queryValue? 0 (GKM.BlowupTwoDoubleExceptionalSingletons.requests j) =
      some (GKM.BlowupTwoDoubleExceptionalSingletons.values j) := by
  obtain ⟨i, k, rfl⟩ : ∃ i k, GKM.BlowupTwoDoubleExceptionalSingletons.index i k = j := by
    revert j
    decide +kernel
  exact (congrArg (fun r ↦ queryValue? 0 r.1 = some r.2)
    (GKM.BlowupTwoDoubleExceptionalSingletons.binding i k)).mpr
    (AxiomaticGW.BlowupTwoDoubleExceptionalSingletons.accepted i
      (BlowupTwoExceptionalOneMarking.labels k))

/-- Lookup in the ten original mixed singleton reconstructions on these two axes. -/
def singleton? := singletonTable? GKM.BlowupTwoDoubleExceptionalSingletons.requests
  GKM.BlowupTwoDoubleExceptionalSingletons.values

/-- Replay a singleton, point-support receipt, or an original marked-pair reduction. -/
def targetValue? (q : SurfaceQuery .blowupTwo) : Option ℚ :=
  (singleton? q).orElse fun _ ↦ supportedMarkedPairValueWith? singleton? q

private theorem targetValue_sound (q : SurfaceQuery .blowupTwo) (v : ℚ)
    (hv : targetValue? q = some v) : CheckedDescendant 0 q v := by
  have one : ∀ t w, singleton? t = some w → queryValue? 0 t = some w :=
    singletonTable?_sound singletons
  cases hs : singleton? q with
  | none =>
    exact supportedMarkedPairValueWith?_checked 0 one
      (by simpa only [targetValue?, hs, Option.orElse_none] using hv)
  | some a =>
    have ha : a = v := by
      simpa only [targetValue?, hs, Option.orElse_some, Option.some.injEq] using hv
    exact .mixed (one _ _ (ha ▸ hs))

/-- The native rows for which one of the original target-side deductions succeeds. -/
def targetRows : Finset (Fin 210) := Finset.univ.filter (fun j ↦ (targetValue? (requests j)).isSome)

/-- The remaining 64 rows require an interior two-positive-power reduction on Bl₂. -/
theorem card_targetRows : targetRows.card = 146 := by decide +kernel

private theorem agrees : ∀ j : Fin 210, (targetValue? (requests j)).all (· == values j) = true := by
  decide +kernel

/-- On every covered row the original Bl₂ computation, full field and specialization agree. -/
theorem target_certified {j : Fin 210} (h : j ∈ targetRows) :
    CheckedDescendant 0 (requests j) (values j) ∧
    equivariant j = (values j : EquivariantCoefficients.Coefficient) ∧
    EquivariantCoefficients.Specializes (equivariant j) (values j) := by
  have hv := (Finset.mem_filter.mp h).2
  obtain ⟨v, he⟩ := Option.isSome_iff_exists.mp hv
  have ha := agrees j
  simp only [he, Option.all_some, beq_iff_eq] at ha
  exact ⟨targetValue_sound _ _ (ha ▸ he), equivariant_eq_ordinary j, specializes j⟩

end AxiomaticGW.GKM.BlowupTwoDoubleExceptionalFewMarkings
