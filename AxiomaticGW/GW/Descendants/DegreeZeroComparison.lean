/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.MixedComparison

/-!
# Degree-zero descendant--ancestor comparison

A zero effective class has no positive rational-tail splitting. Transferring
each stable-map cotangent power therefore only increases the corresponding
ancestor power. This proves the comparison for every finite stable marking
set directly from the primitive rational-tail geometry, without calibration
values or a supplied descendant--ancestor identity.
-/

@[expose] public section

namespace AxiomaticGW.RationalTailIntersection

universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {T : StableMapStabilization G} {P : PsiClasses C}

/-- In class zero, both cotangent families combine into the ancestor monomial.
The induction decreases the sum of stable-map powers, retaining all labels. -/
theorem mixedInvariant_zero_class (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (d e : S → ℕ) (a : S → V) :
    M.mixedInvariant P I g S h 0 d e a =
      Omega.ancestorInvariant P I g S h 0 (d + e) a := by
  classical
  have hz : D.positiveTailSplittings 0 = ∅ := by
    rw [EffectiveCurveMonoid.positiveTailSplittings, D.splittings_zero]
    simp only [ne_eq, not_true_eq_false, Finset.filter_singleton, if_false]
  haveI : IsEmpty ↥(D.positiveTailSplittings 0) := by rw [hz]; infer_instance
  induction hn : ∑ s, d s using Nat.strong_induction_on generalizing d e with
  | h n ih =>
    by_cases hd : d = 0
    · subst d
      simp only [M.mixedInvariant_zero_descendant, zero_add]
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra! hz
        exact hd (funext hz)
      have hpower : d s - 1 + 1 = d s := by omega
      have hlt : (∑ t, Function.update d s (d s - 1) t) < n := by
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro t _
          by_cases ht : t = s
          · subst t
            simp only [Function.update_self]
            omega
          · rw [Function.update_of_ne ht]
        · exact ⟨s, Finset.mem_univ s, by
            simp only [Function.update_self]
            omega⟩
      have hstep := K.mixed_step_at g S h s 0 (d s - 1) d e a
      simp only [hpower, Function.update_eq_self, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero] at hstep
      have hnext := ih _ hlt (Function.update d s (d s - 1))
        (Function.update e s (e s + 1)) rfl
      have hsum : Function.update d s (d s - 1) +
          Function.update e s (e s + 1) = d + e := by
        funext t
        by_cases ht : t = s
        · subst t
          simp only [Pi.add_apply, Function.update_self]
          omega
        · simp only [Pi.add_apply, Function.update_of_ne ht]
      rw [hsum] at hnext
      exact hstep.trans hnext

/-- Stable degree-zero descendants equal ancestors with the same powers.
Curve-unstable degree-zero conventions are deliberately outside this statement. -/
theorem invariant_zero_class (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (d : S → ℕ) (a : S → V) :
    M.invariant I g S h 0 d a = Omega.ancestorInvariant P I g S h 0 d a := by
  simpa only [M.mixedInvariant_zero_ancestor, add_zero] using
    K.mixedInvariant_zero_class g S h d 0 a

end AxiomaticGW.RationalTailIntersection
