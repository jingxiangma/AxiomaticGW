/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.MixedAncestorReduction

/-!
# Bounded table substitution in descendant comparison

Every rational-tail cut retains a main class of no larger energy. A bounded
ancestor table therefore suffices to evaluate the complete mixed expression
at any class in its range. Full curve coordinates and all insertions remain
unchanged by the congruence; energy only controls the lookup bound.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceTarget

theorem positiveTailSplittings_main_energy_le (X : SurfaceTarget) (beta : X.Curve)
    {split : X.Curve × X.Curve} (hs : split ∈ X.positiveTailSplittings beta) :
    X.effective.energy split.1 ≤ X.effective.energy beta := by
  rw [X.positiveTailSplittings_eq, X.effective.mem_positiveTailSplittings] at hs
  have he := congrArg X.effective.energy hs.1
  rw [map_add] at he
  omega

end SurfaceTarget

namespace SurfaceDescendant

/-- Transfer at one marking only consults the continuation within the same bound. -/
theorem eval_transferMark_congr_of_energy_le {X : SurfaceTarget} {S : Type} [DecidableEq S]
    (v w : SurfaceAncestorKey X → ℚ) (bound : ℕ) (s : S)
    (next : X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms (SurfaceAncestorKey X))
    (hn : ∀ beta, X.effective.energy beta ≤ bound → ∀ e a,
      RationalTerms.eval v (next beta e a) = RationalTerms.eval w (next beta e a))
    (m : ℕ) (beta : X.Curve) (e : S → ℕ) (a : S → SurfaceBasisLabel X)
    (hb : X.effective.energy beta ≤ bound) :
    RationalTerms.eval v (transferMark s next m beta e a) =
      RationalTerms.eval w (transferMark s next m beta e a) := by
  induction m generalizing e with
  | zero => exact hn beta hb e a
  | succ m ih =>
    simp only [transferMark, RationalTerms.eval_add, RationalTerms.eval_sum,
      RationalTerms.eval_scale, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro split hs
    apply Finset.sum_congr rfl
    intro b _
    rw [hn split.1 ((X.positiveTailSplittings_main_energy_le beta hs).trans hb)]

/-- Ancestor replacement requires agreement only through the input energy. -/
theorem eval_mixedAncestorTerms_congr_of_energy_le {X : SurfaceTarget}
    (v w : SurfaceAncestorKey X → ℚ) (bound : ℕ)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S)
    (hv : ∀ beta, X.effective.energy beta ≤ bound → ∀ e a,
      v (SurfaceAncestorKey.ofLabels g S h beta e a) =
        w (SurfaceAncestorKey.ofLabels g S h beta e a))
    (marks : List S) (beta : X.Curve) (d e : S → ℕ) (a : S → SurfaceBasisLabel X)
    (hb : X.effective.energy beta ≤ bound) :
    RationalTerms.eval v (mixedAncestorTerms g S h marks beta d e a) =
      RationalTerms.eval w (mixedAncestorTerms g S h marks beta d e a) := by
  induction marks generalizing beta d e a with
  | nil =>
    simp only [mixedAncestorTerms, RationalTerms.eval_term, Multiset.map_singleton,
      Multiset.prod_singleton, hv beta hb]
  | cons s marks ih =>
    rw [mixedAncestorTerms]
    exact eval_transferMark_congr_of_energy_le v w bound s _
      (fun b hbound e' a' ↦ ih b _ e' a' hbound) (d s) beta e a hb

end SurfaceDescendant
end AxiomaticGW
