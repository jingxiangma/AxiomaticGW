/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroCompactStep

/-!
# Certified bounded tables for primary genus zero

Each energy layer evaluates its equations using a previously computed table.
Entries retain the full curve class, and lookup is an exact finite sum. The
agreement theorem with `pointValue` proves completeness and excludes use of
any missing lower-class entry. Binomial compression evaluates the same original
marked equation without enumerating its ordered point placements.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- Lookup by the entire curve class. The table construction gives one entry per class. -/
def tableLookup {X : SurfaceTarget} (table : Multiset (X.Curve × ℚ)) (beta : X.Curve) : ℚ :=
  (table.map (fun t ↦ if t.1 = beta then t.2 else 0)).sum

private theorem tableLookup_map {X : SurfaceTarget} (d : ℕ) (v : X.Curve → ℚ)
    (beta : X.Curve) (h : X.effective.energy beta ≤ d) :
    tableLookup ((X.bounded d).val.map (fun b ↦ (b, v b))) beta = v beta := by
  have hb : beta ∈ X.bounded d := by
    rw [SurfaceTarget.bounded_eq, X.effective.mem_bounded]
    exact h
  unfold tableLookup
  rw [Multiset.map_map]
  change (∑ b ∈ X.bounded d, if b = beta then v b else 0) = v beta
  rw [Finset.sum_eq_single_of_mem beta hb]
  · exact if_pos rfl
  · intro b _ hne
    exact if_neg hne

/-- Exact bounded values computed one energy layer at a time. Each previous
table is shared by every lookup in the next layer, so lower invariants are reused. -/
def pointTable (X : SurfaceTarget) : ℕ → Multiset (X.Curve × ℚ)
  | 0 => (X.bounded 0).val.map (fun beta ↦ (beta, initialValue X beta))
  | d + 1 =>
      let previous := pointTable X d
      (X.bounded (d + 1)).val.map (fun beta ↦ (beta,
        if X.effective.energy beta ≤ d then tableLookup previous beta else
        if IsInitial X beta then initialValue X beta else
          compactReconstructionStep X beta (fun v ↦ tableLookup previous (variableCurve v))))

/-- The bounded computation agrees with the well-founded evaluator on every
class in its bound. No external table or truncated dependency assumption is used. -/
theorem tableLookup_pointTable (X : SurfaceTarget) (d : ℕ) (beta : X.Curve)
    (h : X.effective.energy beta ≤ d) : tableLookup (pointTable X d) beta = pointValue X beta := by
  induction d generalizing beta with
  | zero =>
      rw [pointTable, tableLookup_map 0 _ beta h]
      exact (pointValue_initial X beta (Or.inl (by omega))).symm
  | succ d ih =>
      rw [pointTable, tableLookup_map (d + 1) _ beta h]
      by_cases hold : X.effective.energy beta ≤ d
      · rw [if_pos hold]
        exact ih beta hold
      rw [if_neg hold]
      by_cases hinit : IsInitial X beta
      · rw [if_pos hinit, pointValue_initial X beta hinit]
      · rw [if_neg hinit, compactReconstructionStep_eq X beta hinit, pointValue_step X beta hinit]
        congr 2
        apply RationalTerms.eval_congr
        intro t ht v hv
        obtain ⟨gamma, _, rfl, hlt⟩ := reconstructionRemainder_dependencies X beta t ht v hv
        exact ih gamma (by omega)

/-- Compute a point value using all lower energy layers once per layer. -/
def cachedPointValue (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  tableLookup (pointTable X (X.effective.energy beta)) beta

theorem cachedPointValue_eq (X : SurfaceTarget) (beta : X.Curve) :
    cachedPointValue X beta = pointValue X beta := tableLookup_pointTable X _ beta le_rfl

/-- The same arbitrary-primary interface with certified reuse of lower point values. -/
def cachedPrimaryValue (X : SurfaceTarget) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : ℚ :=
  if beta = 0 then SurfacePrimary.classicalValue m else
    if m.count .point = X.effective.energy beta - 1 then
      (m.map (SurfaceBasisLabel.primaryFactor beta)).prod * cachedPointValue X beta
    else 0

theorem cachedPrimaryValue_eq (X : SurfaceTarget) (beta : X.Curve)
    (m : Multiset (SurfaceBasisLabel X)) : cachedPrimaryValue X beta m = primaryValue X beta m := by
  simp only [cachedPrimaryValue, primaryValue, cachedPointValue_eq]

end AxiomaticGW.SurfaceGenusZero
