/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PointPullbackContraction
public import AxiomaticGW.Surfaces.GenusZeroExpansion

/-!
# Primary vertices in signed point pullback

A component without cotangent decorations acquires no signed rational tails.
Its point pullback is its original primary value with the added points in the
insertion multiset. The terminal-value hypothesis states precisely the needed
independence of the finite label presentation.
-/

@[expose] public section

namespace AxiomaticGW.SurfacePointPullback

/-- A dimension-selected right component collapses the placement sum. When
`k > n`, the binomial coefficient is zero; no truncated count contributes. -/
theorem sum_binomial_of_right_support {A : Type*} [CommRing A]
    (f r : ℕ → A) (n k : ℕ) (hr : ∀ j, j ≠ k → r j = 0) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (n.choose ij.1 : A) * (f ij.1 * r ij.2)) =
      (n.choose k : A) * (f (n - k) * r k) := by
  by_cases hk : k ≤ n
  · have hm : (n - k, k) ∈ Finset.HasAntidiagonal.antidiagonal n := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      exact Nat.sub_add_cancel hk
    rw [Finset.sum_eq_single_of_mem (n - k, k) hm, Nat.choose_symm hk]
    intro ij hij hne
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hj : ij.2 ≠ k := by
      intro he
      apply hne
      apply Prod.ext
      · dsimp only
        omega
      · exact he
    rw [hr ij.2 hj, mul_zero, mul_zero]
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < k), Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [hr ij.2 (by omega), mul_zero, mul_zero]

/-- Zero cotangent powers reduce the signed recursion to one primary key. -/
theorem vertex_primary_eq {A : Type*} [CommRing A] [Algebra ℚ A]
    (X : SurfaceTarget) (value : SurfaceVertexValues X A)
    (f : SurfaceAncestorKey X → A) (g : ℕ)
    (hf : ∀ (S : Type) [Fintype S] (h : StableArity g S) (beta : X.Curve)
      (a : S → SurfaceBasisLabel X),
      value g S h beta 0 a = f (SurfaceAncestorKey.ofLabels g S h beta 0 a))
    (n : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    vertex X value n g S h 0 l beta a =
      f ((SurfaceAncestorKey.ofLabels g S h beta 0 a).addPoints n) := by
  induction n generalizing S with
  | zero => simp only [vertex, hf, SurfaceAncestorKey.addPoints_zero]
  | succ n ih =>
    rw [vertex_succ]
    simp only [GluingExpression.addCotangentMarking, Pi.zero_apply, ne_eq,
      not_true_eq_false, Finset.filter_false, Finset.empty_val, Multiset.map_zero,
      add_zero, Multiset.map_singleton, Multiset.sum_singleton, Int.cast_one,
      one_mul, GluingExpression.CotangentTerm.fundamental,
      GluingExpression.pointContraction]
    have hz : (fun s : Option S ↦ s.elim 0 (0 : S → ℕ)) = 0 := by
      funext s
      cases s <;> rfl
    rw [hz, ih, SurfaceAncestorKey.addPoints_ofLabels_option g S h beta a n]

end AxiomaticGW.SurfacePointPullback
