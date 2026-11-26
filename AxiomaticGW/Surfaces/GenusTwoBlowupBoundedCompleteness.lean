/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupBoundedCertificate

/-!
# Completeness of the bounded canonical reconstruction checker

The checker reads a candidate only at canonical states in the energy grid.
Consequently any independent proof of the values on that grid provides
a certificate for the original full-row checker, regardless of how the
candidate is defined at higher energies.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupBoundedCertificate
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction SurfaceGenusTwoBlowupScalar

/-- The executable table accepts exactly the well-founded values on its full energy grid. -/
theorem checkTable_iff {X : SurfaceTarget} (i : Fin X.blowups) (B : ℕ)
    (candidate : State X → ℚ) :
    checkTable i B candidate = true ↔
      ∀ s : State X, X.effective.energy s.1 ≤ B →
        candidate s = SurfaceGenusTwoBlowupRecursion.values i s := by
  refine ⟨checkTable_sound i B candidate, ?_⟩
  intro h
  rw [checkTable, List.all_eq_true]
  intro s hs
  by_cases hd : X.planeDegree s.1 = 0
  · rw [checkRow, if_pos hd, decide_eq_true_eq, h s ((mem_states X B s).mp hs)]
    exact SurfaceGenusTwoBlowupRecursion.values_boundary i s hd
  · let v := SurfaceGenusTwoBlowupRecursion.values i
    have hv : ∀ w ∈ columns (states X B),
        canonicalValuation candidate w = canonicalValuation v w := by
      intro w hw
      obtain ⟨t, ht, rfl⟩ := (mem_columns _ _).mp hw
      rw [canonicalValuation_query, canonicalValuation_query]
      exact h t ((mem_states X B t).mp ht)
    rw [checkRow, if_neg hd, decide_eq_true_eq]
    calc
      replay i s (canonicalValuation candidate) (states X B) =
          replay i s (canonicalValuation v) (states X B) := by
        unfold replay
        congr 1
        apply Finset.sum_congr rfl
        intro w hw
        rw [hv w hw]
      _ = _ := (replay_eq_row i B s _ hs (Nat.pos_of_ne_zero hd)).trans
        (SurfaceGenusTwoBlowupRecursion.values_equations i s (Nat.pos_of_ne_zero hd))

end AxiomaticGW.SurfaceGenusTwoBlowupBoundedCertificate
