/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestors

/-!
# Finite certificates for shared genus-two ancestors

Every selected query is checked against the original low-psi terminal family
or the complete square/product equation. The checker also verifies closure
under every residual dependency. Strict psi decrease then identifies all
stored values with the original terminating evaluator. Missing queries use
that evaluator directly, so an incomplete cache cannot change an answer.

This is conditional on the supplied terminal family. The plane consumer uses
its already certified canonical table; the checker does not replace the
surface-specific low-psi reconstruction or introduce numerical seeds.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- The terminating evaluator returns its terminal family at total psi degree at most one. -/
theorem ancestorValue_low (base : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1) :
    ancestorValue base q = base q := by
  unfold ancestorValue
  cases hp : q.totalPsi with
  | zero => rw [ancestorValueFuel, if_pos ⟨hg, hk⟩]
  | succ n => rw [ancestorValueFuel, dif_pos hg, dif_pos hk]

/-- At higher psi degree the evaluator satisfies the complete original boundary equation. -/
theorem ancestorValue_step (base : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2) (hk : 1 < q.totalPsi) :
    ancestorValue base q = ancestorStep (ancestorValue base) q hk := by
  unfold ancestorValue
  cases hp : q.totalPsi with
  | zero => omega
  | succ n =>
    rw [ancestorValueFuel, dif_pos hg, dif_neg (not_le_of_gt hk)]
    apply ancestorStep_congr
    intro r hr hpsi
    exact ancestorValueFuel_stable base n r.totalPsi r hr (by omega) le_rfl

/-- Check the original equation and every dependency of one full ancestor query. -/
def checkAncestorRow (base : SurfaceAncestorKey X → ℚ)
    (queries : Finset (SurfaceAncestorKey X)) (values : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) : Bool :=
  decide (q.genus = 2 ∧ if hk : q.totalPsi ≤ 1 then values q = base q else
    ((ancestorReductionTerms q (by omega)).bind Prod.snd).toFinset ⊆ queries ∧
    values q = ancestorStep values q (by omega))

/-- Check all stored queries, including vanishing rows and their dependency closure. -/
def checkAncestorValues (base : SurfaceAncestorKey X → ℚ)
    (queries : Finset (SurfaceAncestorKey X)) (values : SurfaceAncestorKey X → ℚ) : Bool :=
  decide (∀ q ∈ queries, checkAncestorRow base queries values q = true)

/-- Strict psi descent identifies every accepted entry with the original evaluator. -/
theorem checkAncestorValues_sound (base : SurfaceAncestorKey X → ℚ)
    (queries : Finset (SurfaceAncestorKey X)) (values : SurfaceAncestorKey X → ℚ)
    (hcheck : checkAncestorValues base queries values = true)
    (q : SurfaceAncestorKey X) (hq : q ∈ queries) : values q = ancestorValue base q := by
  simp only [checkAncestorValues, checkAncestorRow, decide_eq_true_eq] at hcheck
  induction q using (measure (fun r : SurfaceAncestorKey X ↦ r.totalPsi)).wf.induction with
  | h q ih =>
    obtain ⟨hg, hv⟩ := hcheck q hq
    by_cases hk : q.totalPsi ≤ 1
    · rw [dif_pos hk] at hv
      rw [ancestorValue_low base q hg hk]
      exact hv
    · rw [dif_neg hk] at hv
      rw [hv.2, ancestorValue_step base q hg (by omega)]
      apply RationalTerms.eval_congr
      intro t ht r hr
      have hm : r ∈ queries := hv.1 (Multiset.mem_toFinset.mpr
        (Multiset.mem_bind.mpr ⟨t, ht, hr⟩))
      have hd := ancestorReductionTerms_dependency q (by omega) ht r hr
      exact ih r hd.2.2.1 hm

/-- Reuse selected values, with the original reconstruction outside the finite cache. -/
def ancestorValueCached (base : SurfaceAncestorKey X → ℚ)
    (queries : Finset (SurfaceAncestorKey X)) (values : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) : ℚ :=
  if q ∈ queries then values q else ancestorValue base q

/-- An accepted finite cache preserves the original evaluator at every query. -/
theorem ancestorValueCached_eq (base : SurfaceAncestorKey X → ℚ)
    (queries : Finset (SurfaceAncestorKey X)) (values : SurfaceAncestorKey X → ℚ)
    (hcheck : checkAncestorValues base queries values = true) :
    ancestorValueCached base queries values = ancestorValue base := by
  funext q
  unfold ancestorValueCached
  split_ifs with hq
  · exact checkAncestorValues_sound base queries values hcheck q hq
  · rfl
end AxiomaticGW.SurfaceGenusTwo
