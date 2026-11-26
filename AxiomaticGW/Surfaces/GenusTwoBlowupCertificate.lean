/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupRecursion

/-!
# Finite certificates for the full-class blowup canonical table

The finite list is checked against the original selected H/P/N/K equations.
After collecting actual cancellations, every variable other than the exact
requested query must name a stored strictly earlier full-class state. Coverage
is checked from the row itself rather than inferred from an output energy bound.
No unlisted candidate entry or ancestor value is trusted by replay.

The checker uses complete polynomial rows. It establishes certificate soundness,
not an efficient scalar implementation or completion of a numerical suite.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupCertificate
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}

-- The selected H equation retains the complete 815-column L24 dispatch.
set_option maxRecDepth 20000

local instance earlierDecidable : DecidableRel (Earlier X) :=
  fun s t ↦ decidable_of_iff _ (earlier_iff X s t).symm

/-- Every variable of the collected complete original equation, with full query keys. -/
def rowVariables (i : Fin X.blowups) (s : State X) : Finset (Variable X) :=
  ((RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)).bind Prod.snd).toFinset

/-- A nonzero collected singleton coefficient supplies an actual full-row variable. -/
theorem mem_rowVariables_of_coefficient_ne_zero (i : Fin X.blowups) (s : State X)
    (v : Variable X)
    (hc : RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s) {v} ≠ 0) :
    v ∈ rowVariables i s := by
  have hm : {v} ∈ RationalTerms.support (SurfaceGenusTwoBlowupRecursion.row i s) := by
    by_contra hn
    exact hc (RationalTerms.coefficient_eq_zero_of_not_mem_support _ _ hn)
  have ht : (RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s) {v}, {v}) ∈
      RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s) :=
    RationalTerms.mem_collect.mpr ⟨hm, rfl, hc⟩
  exact Multiset.mem_toFinset.mpr (Multiset.mem_bind.mpr
    ⟨_, ht, Multiset.mem_singleton.mpr rfl⟩)

/-- A row variable is its exact own query or a listed strictly earlier full state. -/
def checkDependency (states : List (State X)) (s : State X) (v : Variable X) : Bool :=
  decide (v = .inr (s.2.query s.1)) ||
    states.any (fun t ↦ decide (Earlier X t s ∧ v = .inr (t.2.query t.1)))

/-- Decode the finite dependency check without weakening full query equality. -/
theorem checkDependency_eq_true_iff (states : List (State X)) (s : State X)
    (v : Variable X) : checkDependency states s v = true ↔
      v = .inr (s.2.query s.1) ∨
        ∃ t ∈ states, Earlier X t s ∧ v = .inr (t.2.query t.1) := by
  simp only [checkDependency, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]

/-- Verify every collected dependency at its exact full key and strict reconstruction order. -/
def checkClosure (i : Fin X.blowups) (states : List (State X)) (s : State X) : Bool :=
  decide (∀ v ∈ rowVariables i s, checkDependency states s v = true)

/-- Check the proved boundary or the unchanged original equation with finite closure. -/
def checkCanonicalRow (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) (s : State X) : Bool :=
  if X.planeDegree s.1 = 0 then
    decide (candidate s = SurfaceGenusTwoBlowupBoundary.value s.1 s.2)
  else checkClosure i states s &&
    decide (RationalTerms.eval (canonicalValuation candidate)
      (SurfaceGenusTwoBlowupRecursion.row i s) = 0)

/-- Check every stored state, including zero-valued entries and all named dependencies. -/
def checkCanonicalTable (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) : Bool :=
  states.all (checkCanonicalRow i states candidate)

/-- A missing earlier full state cannot be replaced by a same-measure collision. -/
theorem checkClosure_eq_false_of_missing (i : Fin X.blowups) (states : List (State X))
    (s : State X) (v : Variable X) (hv : v ∈ rowVariables i s)
    (hself : v ≠ .inr (s.2.query s.1))
    (hmissing : ∀ t ∈ states, Earlier X t s → v ≠ .inr (t.2.query t.1)) :
    checkClosure i states s = false := by
  apply Bool.eq_false_iff.mpr
  intro hcheck
  rw [checkClosure, decide_eq_true_eq] at hcheck
  rcases (checkDependency_eq_true_iff states s v).mp (hcheck v hv) with hs | ⟨t, ht, he, hq⟩
  · exact hself hs
  · exact hmissing t ht he hq

/-- A positive-plane row rejects a missing actual dependency before trusting its equation. -/
theorem checkCanonicalRow_eq_false_of_missing (i : Fin X.blowups)
    (states : List (State X)) (candidate : State X → ℚ) (s : State X)
    (hd : 0 < X.planeDegree s.1) (v : Variable X) (hv : v ∈ rowVariables i s)
    (hself : v ≠ .inr (s.2.query s.1))
    (hmissing : ∀ t ∈ states, Earlier X t s → v ≠ .inr (t.2.query t.1)) :
    checkCanonicalRow i states candidate s = false := by
  rw [checkCanonicalRow, if_neg (Nat.ne_of_gt hd),
    checkClosure_eq_false_of_missing i states s v hv hself hmissing, Bool.false_and]

/-- The actual reconstruction order forbids a query from being earlier than itself. -/
private theorem own_query_ne_of_earlier (s t : State X) (he : Earlier X t s) :
    (Sum.inr (t.2.query t.1) : Variable X) ≠ .inr (s.2.query s.1) := by
  intro h
  have hs := state_query_injective (Sum.inr.inj h)
  subst t
  rw [earlier_iff] at he
  omega

/-- Every accepted stored value equals the original well-founded reconstruction.
Only actual collected dependencies are required.
No correctness assumption is made about outside candidate values. -/
theorem checkCanonicalTable_sound (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) (hcheck : checkCanonicalTable i states candidate = true)
    (s : State X) (hs : s ∈ states) :
    candidate s = SurfaceGenusTwoBlowupRecursion.values i s := by
  rw [checkCanonicalTable, List.all_eq_true] at hcheck
  induction s using (earlier_wellFounded X).induction with
  | h s ih =>
      have hrow := hcheck s hs
      by_cases hd : X.planeDegree s.1 = 0
      · rw [checkCanonicalRow, if_pos hd, decide_eq_true_eq] at hrow
        rw [SurfaceGenusTwoBlowupRecursion.values_boundary i s hd]
        exact hrow
      · rw [checkCanonicalRow, if_neg hd, Bool.and_eq_true, decide_eq_true_eq] at hrow
        have hclosure := hrow.1
        rw [checkClosure, decide_eq_true_eq] at hclosure
        let other : Variable X → ℚ := fun v ↦
          if v = .inr (s.2.query s.1) then candidate s else
            canonicalValuation (SurfaceGenusTwoBlowupRecursion.values i) v
        have heval : RationalTerms.eval (canonicalValuation candidate)
            (RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)) =
            RationalTerms.eval other
              (RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)) := by
          apply RationalTerms.eval_congr
          intro term ht v hv
          have hmem : v ∈ rowVariables i s :=
            Multiset.mem_toFinset.mpr (Multiset.mem_bind.mpr ⟨term, ht, hv⟩)
          rcases (checkDependency_eq_true_iff states s v).mp (hclosure v hmem) with
            hself | ⟨t, ht, he, hq⟩
          · rw [hself, canonicalValuation_query]
            change candidate s = if _ then candidate s else _
            rw [if_pos rfl]
          · rw [hq, canonicalValuation_query]
            change candidate t = if _ then candidate s else _
            rw [if_neg (own_query_ne_of_earlier s t he), canonicalValuation_query]
            exact ih t he ht
        have heq : RationalTerms.eval other (SurfaceGenusTwoBlowupRecursion.row i s) = 0 := by
          rw [← RationalTerms.eval_collect other _, ← heval, RationalTerms.eval_collect]
          exact hrow.2
        have hp : 0 < X.planeDegree s.1 := Nat.pos_of_ne_zero hd
        calc
          candidate s = other (.inr (s.2.query s.1)) := by
            change candidate s = if _ then candidate s else _
            rw [if_pos rfl]
          _ = SurfaceGenusTwoBlowupRecursion.step i other s :=
            SurfaceGenusTwoBlowupRecursion.value_eq_step i other s hp heq
          _ = SurfaceGenusTwoBlowupRecursion.step i
              (canonicalValuation (SurfaceGenusTwoBlowupRecursion.values i)) s := by
            apply SurfaceGenusTwoBlowupRecursion.step_congr i _ _ s hp
            intro t he
            change (if _ then candidate s else _) = _
            rw [if_neg (own_query_ne_of_earlier s t he)]
          _ = SurfaceGenusTwoBlowupRecursion.values i s :=
            (SurfaceGenusTwoBlowupRecursion.values_step i s hp).symm

/-- Reuse accepted entries and preserve the original reconstruction outside the finite list. -/
def valuesCached (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) (s : State X) : ℚ :=
  if states.any (fun t ↦ decide (t.2.query t.1 = s.2.query s.1)) then candidate s else
    SurfaceGenusTwoBlowupRecursion.values i s

/-- Accepted full-key cache entries preserve every request, including unlisted states. -/
theorem valuesCached_eq (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) (hcheck : checkCanonicalTable i states candidate = true) :
    valuesCached i states candidate = SurfaceGenusTwoBlowupRecursion.values i := by
  funext s
  unfold valuesCached
  split_ifs with hs
  · obtain ⟨t, ht, he⟩ := List.any_eq_true.mp hs
    rw [decide_eq_true_eq] at he
    have ht' := state_query_injective he
    subst t
    exact checkCanonicalTable_sound i states candidate hcheck s ht
  · rfl

/-- Bind replay to the complete dimension-compatible canonical query and claimed value.
The nominal class-zero point-descendant state remains internal to the table. -/
def checkCanonicalClaim (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) (q : SurfaceQuery X) (claimed : ℚ) : Bool :=
  decide q.DimensionCompatible &&
    states.any (fun s ↦ decide (q = s.2.query s.1 ∧ candidate s = claimed)) &&
      checkCanonicalTable i states candidate

/-- An accepted claim identifies the exact query and the original reconstructed value. -/
theorem checkCanonicalClaim_sound (i : Fin X.blowups) (states : List (State X))
    (candidate : State X → ℚ) (q : SurfaceQuery X) (claimed : ℚ)
    (hcheck : checkCanonicalClaim i states candidate q claimed = true) :
    q.DimensionCompatible ∧ ∃ s ∈ states, q = s.2.query s.1 ∧
      SurfaceGenusTwoBlowupRecursion.values i s = claimed := by
  rw [checkCanonicalClaim, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at hcheck
  obtain ⟨s, hs, hclaim⟩ := hcheck.1.2
  rw [decide_eq_true_eq] at hclaim
  refine ⟨hcheck.1.1, s, hs, hclaim.1, ?_⟩
  rw [← checkCanonicalTable_sound i states candidate hcheck.2 s hs]
  exact hclaim.2

end AxiomaticGW.SurfaceGenusTwoBlowupCertificate
