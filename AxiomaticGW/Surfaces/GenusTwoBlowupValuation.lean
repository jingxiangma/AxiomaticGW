/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupOrder

/-!
# Exact canonical state lookup for the blowup reconstruction

The reconstruction order uses full curve classes and the H/P/N/K sectors.
This executable decoder checks the complete canonical query before recovering
its state. Its inverse theorem rules out collisions between distinct classes
or exceptional labels, even when their reconstruction measures coincide.

The table extension supplies zero on other variables. This is justified on
selected polynomial rows only by their separate canonical support theorems;
it is not a descendant evaluator. The nominal class-zero P state is retained
as a table index and remains dimension incompatible.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupOrder
open SurfacePolynomialReduction
variable {X : SurfaceTarget}

/-- Decode the exact canonical shape, retaining the full curve and exceptional label.
The nominal class-zero P state is included; this is not a dimension or geometric-domain check. -/
def state? (q : SurfaceQuery X) : Option (State X) :=
  let candidate : Option (Family X) := match q.insertions.head? with
    | some ⟨.hyperplane, 1⟩ => some .hyperplane
    | some ⟨.point, 1⟩ => some .point
    | some ⟨.point, 0⟩ => some .primary
    | some ⟨.exceptional i, 1⟩ => some (.exceptional i)
    | _ => none
  candidate.bind fun f ↦ if f.query q.beta = q then some (q.beta, f) else none

/-- Decoding every canonical shape recovers its original state. -/
theorem state?_query (f : Family X) (beta : X.Curve) :
    state? (f.query beta) = some (beta, f) := by
  cases f <;> simp only [state?, Family.query, SurfaceFirstDescendant.query,
    SurfaceQuery.points, List.head?_cons, List.replicate_succ, Option.bind_some, ite_true]

/-- A decoded state asserts equality of the whole request, not merely its first insertion. -/
theorem state?_eq_some_iff (q : SurfaceQuery X) (s : State X) :
    state? q = some s ↔ s.2.query s.1 = q := by
  constructor
  · intro h
    unfold state? at h
    split at h <;> simp only [Option.bind_some, Option.bind_none] at h
    all_goals first
      | cases h
      | split_ifs at h with he
        have hs := Option.some.inj h
        rw [← hs]
        exact he
  · intro h
    rw [← h, state?_query]

/-- Distinct full classes or exceptional labels cannot collide in a query table. -/
theorem state_query_injective : Function.Injective (fun s : State X ↦ s.2.query s.1) := by
  intro s t h
  have he := congrArg state? h
  rw [state?_query, state?_query] at he
  exact Option.some.inj he

/-- Extend a canonical table to polynomial variables. Ancestors and noncanonical
requests receive zero; support theorems justify its use on selected BP/L24 rows. -/
def canonicalValuation (values : State X → ℚ) : Variable X → ℚ
  | .inl _ => 0
  | .inr q => match state? q with
    | some s => values s
    | none => 0

/-- The extension preserves every canonical table entry, including both exceptional labels. -/
theorem canonicalValuation_query (values : State X → ℚ) (f : Family X) (beta : X.Curve) :
    canonicalValuation values (.inr (f.query beta)) = values (beta, f) := by
  simp only [canonicalValuation, state?_query]

end AxiomaticGW.SurfaceGenusTwoBlowupOrder
