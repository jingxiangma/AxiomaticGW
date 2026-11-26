/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupUnitPairs

/-! # Reconstructing marked pairs from a partial table of proved singleton descendants

The string, dilaton and primary-divisor equations need at most two singleton queries.
A table can supply any previously certified singleton with the exact requested class and
insertion. A vanishing divisor coefficient needs no table entry.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceGenusTwoBlowupDescendants
variable {X : SurfaceTarget}

/-- Look up a previously certified singleton using its complete surface query. -/
def singletonTable? {n : ℕ} (requests : Fin n → SurfaceQuery X) (values : Fin n → ℚ)
    (q : SurfaceQuery X) : Option ℚ :=
  ((List.finRange n).find? (fun j ↦ decide (requests j = q))).map values

/-- A returned table entry computes the value at the original class and ordered insertions. -/
theorem singletonTable?_sound {n : ℕ} {requests : Fin n → SurfaceQuery X} {values : Fin n → ℚ}
    {i : Fin X.blowups} (accepted : ∀ j, queryValue? i (requests j) = some (values j))
    (q : SurfaceQuery X) (v : ℚ) (h : singletonTable? requests values q = some v) :
    queryValue? i q = some v := by
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  have hq : requests j = q :=
    of_decide_eq_true (List.find?_some (p := fun k ↦ decide (requests k = q)) hj)
  rw [← hq]
  exact accepted j

/-- Evaluate the recognized marked equation using the supplied partial singleton evaluator. -/
def markedPairValueWith? (one : SurfaceQuery X → Option ℚ) (q : SurfaceQuery X) : Option ℚ :=
  match unitPairReduction? q with
  | some (rule, s) => (one ⟨2, q.beta, [s]⟩).map (rule.factor * ·)
  | none => divisorPairValueWith? one q

private theorem weighted_of_partial {one actual : SurfaceQuery X → Option ℚ}
    (h : ∀ q v, one q = some v → actual q = some v)
    {c v : ℚ} {beta : X.Curve} {s : SurfaceInsertion X}
    (hv : weightedSingleton? one c beta s = some v) :
    weightedSingleton? actual c beta s = some v := by
  by_cases hc : c = 0
  · simpa only [weightedSingleton?, if_pos hc] using hv
  · simp only [weightedSingleton?, if_neg hc, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨a, ha, heq⟩ := hv
    exact ⟨a, h _ _ ha, heq⟩

/-- Successful lookup proves one of the original marked reductions on the ordered query. -/
theorem markedPairValueWith?_checked (i : Fin X.blowups) {one : SurfaceQuery X → Option ℚ}
    (h : ∀ q v, one q = some v → queryValue? i q = some v) {q : SurfaceQuery X} {v : ℚ}
    (hv : markedPairValueWith? one q = some v) : CheckedDescendant i q v := by
  cases hu : unitPairReduction? q with
  | some p =>
    obtain ⟨rule, s⟩ := p
    simp only [markedPairValueWith?, hu, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, heq⟩ := hv
    apply CheckedDescendant.unitPair
    simp only [unitPairValue?, hu, Option.map_eq_some_iff]
    exact ⟨a, h _ _ ha, heq⟩
  | none =>
    apply CheckedDescendant.divisorPair
    cases hd : divisorPairReduction? q with
    | none => simp only [markedPairValueWith?, hu, divisorPairValueWith?, hd, reduceCtorEq] at hv
    | some p =>
      obtain ⟨d, s⟩ := p
      simp only [markedPairValueWith?, hu, divisorPairValueWith?, hd, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hv
      simp only [divisorPairValue?, divisorPairValueWith?, hd, Option.bind_eq_some_iff,
        Option.map_eq_some_iff]
      obtain ⟨a, ha, b, hb, heq⟩ := hv
      exact ⟨a, weighted_of_partial h ha, b, weighted_of_partial h hb, heq⟩

/-- Use exceptional point support first, then the marked equations with a partial evaluator. -/
def supportedMarkedPairValueWith? (one : SurfaceQuery X → Option ℚ) (q : SurfaceQuery X) :
    Option ℚ :=
  match exceptionalPointQueryValue? q with
  | some v => some v
  | none => markedPairValueWith? one q

/-- Each accepted value has the corresponding original support or reconstruction witness. -/
theorem supportedMarkedPairValueWith?_checked (i : Fin X.blowups) {one : SurfaceQuery X → Option ℚ}
    (h : ∀ q v, one q = some v → queryValue? i q = some v) {q : SurfaceQuery X} {v : ℚ}
    (hv : supportedMarkedPairValueWith? one q = some v) : CheckedDescendant i q v := by
  cases he : exceptionalPointQueryValue? q with
  | none =>
    simp only [supportedMarkedPairValueWith?, he] at hv
    exact markedPairValueWith?_checked i h hv
  | some w =>
    simp only [supportedMarkedPairValueWith?, he, Option.some.injEq] at hv
    exact .exceptionalPoint (hv ▸ he)

end AxiomaticGW.SurfaceGenusTwo
