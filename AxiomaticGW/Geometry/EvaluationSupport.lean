/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Geometry.StableMapIntersection
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Vanishing from evaluation support

A zero evaluation pullback kills the complete stable-map integrand, regardless
of the cotangent powers or the remaining states. Linear virtual integration
then gives vanishing of the existing numerical invariant. The vanishing
pullback is an explicit geometric premise; no numerical value is assumed.
-/

@[expose] public section

namespace AxiomaticGW.StableMapIntersection
universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I}

/-- One vanishing evaluation factor annihilates the whole decorated integrand. -/
theorem integrand_eq_zero_of_evaluation_eq_zero (G : StableMapIntersection U)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (d : S → ℕ) (a : S → V) (s : S)
    (h : G.evaluation g S beta s (a s) = 0) :
    G.integrand g S beta d a = 0 := by
  classical
  unfold integrand
  exact Finset.prod_eq_zero (Finset.mem_univ s) (by rw [h, mul_zero])

/-- Virtual integration is linear, so a zero evaluation factor gives an exact zero. -/
theorem invariant_eq_zero_of_evaluation_eq_zero (G : StableMapIntersection U)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (d : S → ℕ) (a : S → V) (s : S)
    (h : G.evaluation g S beta s (a s) = 0) : U.invariant g S beta d a = 0 := by
  rw [← G.numerical]
  change G.integrate g S beta (G.integrand g S beta d a) = 0
  rw [G.integrand_eq_zero_of_evaluation_eq_zero g S beta d a s h, map_zero]

end AxiomaticGW.StableMapIntersection
