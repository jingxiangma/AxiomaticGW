/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Geometry.StableMapIntersection

/-!
# Mixed cotangent comparison from virtual boundary geometry

The distinguished marking is `none : Option S`. On a contracted rational
tail, it becomes marking `1 : Fin 2`; marking `0` is the attaching node.
On the main component, `none` is the replacement node. All other labels and
ancestor powers remain on that component.

The boundary source is a separate fiber-product cohomology algebra. There
is no false pullback from the target to the unrestricted product of moduli
spaces. The virtual diagonal law evaluates products of component pullbacks
by the canonical inverse metric. Together with the primitive cotangent
cycle identity, these laws derive Kontsevich--Manin (alg-geom/9708024), (4).
No solved numerical recurrence is a field of the geometric input.
-/

@[expose] public section

namespace AxiomaticGW
open TensorProduct
universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {P : PsiClasses C}

/-- Primitive geometry of the positive-degree rational tail contracted at `none`.
The cotangent identity concerns arbitrary ambient classes, and the diagonal law
concerns arbitrary component classes, independently of descendant exponents. -/
structure RationalTailIntersection (G : StableMapIntersection U)
    (T : StableMapStabilization G) (P : PsiClasses C) where
  /-- Cohomology of the fiber product over the target's node evaluation maps. -/
  H : ∀ (_g : ℕ) (S : Type) [Fintype S] (_h : StableArity _g (Option S)) (beta : B),
    ↥(D.positiveTailSplittings beta) → EvenGradedAlgebra R
  /-- Restriction from the glued stable-map space to its boundary. -/
  pull : ∀ g S [Fintype S] h beta split,
    G.H g (Option S) beta →ₐ[R] H g S h beta split
  /-- Pullback from the main component. Its replacement node is `none`. -/
  main : ∀ g S [Fintype S] h beta split,
    G.H g (Option S) split.val.1 →ₐ[R] H g S h beta split
  /-- Pullback from the two-point rational tail, with node `0` and retained marking `1`. -/
  tail : ∀ g S [Fintype S] h beta split,
    G.H 0 (Fin 2) split.val.2 →ₐ[R] H g S h beta split
  /-- Integration against the virtual boundary cycle. -/
  integrate : ∀ g S [Fintype S] h beta split, H g S h beta split →ₗ[R] R
  /-- The distinguished evaluation is on the retained tail marking. -/
  evaluation_none : ∀ g S [Fintype S] h beta split x,
    pull g S h beta split (G.evaluation g (Option S) beta none x) =
      tail g S h beta split (G.evaluation 0 (Fin 2) split.val.2 1 x)
  /-- Every other evaluation stays at its original main-component label. -/
  evaluation_some : ∀ g S [Fintype S] h beta split s x,
    pull g S h beta split (G.evaluation g (Option S) beta (some s) x) =
      main g S h beta split (G.evaluation g (Option S) split.val.1 (some s) x)
  /-- The distinguished stable-map cotangent line restricts to the tail. -/
  psi_none : ∀ g S [Fintype S] h beta split,
    pull g S h beta split (G.psi g (Option S) beta none) =
      tail g S h beta split (G.psi 0 (Fin 2) split.val.2 1)
  /-- The other stable-map cotangent lines restrict to the main component. -/
  psi_some : ∀ g S [Fintype S] h beta split s,
    pull g S h beta split (G.psi g (Option S) beta (some s)) =
      main g S h beta split (G.psi g (Option S) split.val.1 (some s))
  /-- Stabilization of the boundary is stabilization of its main component,
  including the ancestor cotangent line at its replacement node. -/
  stabilization : ∀ g S [Fintype S] h beta split (x : C.H g (Option S)),
    pull g S h beta split (T.pull g (Option S) h beta x) =
      main g S h beta split (T.pull g (Option S) h split.val.1 x)
  /-- Virtual refined diagonal splitting for arbitrary component decorations. -/
  diagonal : ∀ g S [Fintype S] h beta split
      (x : G.H g (Option S) split.val.1) (y : G.H 0 (Fin 2) split.val.2),
    integrate g S h beta split (main g S h beta split x * tail g S h beta split y) =
      TensorProduct.lift (((LinearMap.mul R R).comp
        (G.nodeIntegral g (Option S) split.val.1 none x)).compl₂
          (G.nodeIntegral 0 (Fin 2) split.val.2 0 y)) Omega.pairing.copairing
  /-- The virtual cotangent cycle identity, paired with any ambient class.
  Ordered gluing has coefficient one; each split has strictly positive tail class. -/
  cotangent : ∀ g S [Fintype S] h beta (x : G.H g (Option S) beta),
    G.integrate g (Option S) beta (x * (G.psi g (Option S) beta none -
      T.pull g (Option S) h beta (P.psi g (Option S) h none))) =
        ∑ split : ↥(D.positiveTailSplittings beta),
          integrate g S h beta split (pull g S h beta split x)

namespace RationalTailIntersection
variable {T : StableMapStabilization G}

/-- Cotangent and evaluation pullbacks factor the actual mixed decoration.
The main node has no descendant power, while every ancestor power remains. -/
theorem pull_mixed_integrand (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g (Option S)) (beta : B)
    (split : ↥(D.positiveTailSplittings beta))
    (m : ℕ) (d : S → ℕ) (e : Option S → ℕ) (y : V) (a : S → V) :
    K.pull g S h beta split
        (G.integrand g (Option S) beta (Option.casesOn · m d) (Option.casesOn · y a) *
          T.pull g (Option S) h beta (P.monomial g (Option S) h e)) =
      K.main g S h beta split
        ((∏ s, G.psi g (Option S) split.val.1 (some s) ^ d s *
          G.evaluation g (Option S) split.val.1 (some s) (a s)) *
          T.pull g (Option S) h split.val.1 (P.monomial g (Option S) h e)) *
        K.tail g S h beta split
          (G.psi 0 (Fin 2) split.val.2 1 ^ m * G.evaluation 0 (Fin 2) split.val.2 1 y) := by
  simp only [StableMapIntersection.integrand, Fintype.prod_option,
    map_mul, map_prod, map_pow, K.psi_none, K.psi_some,
    K.evaluation_none, K.evaluation_some, K.stabilization]
  ring

/-- Virtual boundary evaluation inserts the actual two-point calibration state
in the existing mixed invariant of the main component. -/
theorem integrated_tail (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g (Option S)) (beta : B)
    (split : ↥(D.positiveTailSplittings beta))
    (m : ℕ) (d : S → ℕ) (e : Option S → ℕ) (y : V) (a : S → V) :
    K.integrate g S h beta split (K.pull g S h beta split
        (G.integrand g (Option S) beta (Option.casesOn · m d) (Option.casesOn · y a) *
          T.pull g (Option S) h beta (P.monomial g (Option S) h e))) =
      M.mixedInvariant P I g (Option S) h split.val.1 (Option.casesOn · 0 d) e
        (Option.casesOn · (U.calibrationCoefficient (m+1) split.val.2 y) a) := by
  rw [K.pull_mixed_integrand, K.diagonal, G.nodeIntegral_twoPoint,
    U.calibrationCoefficient_contract, T.nodeIntegral_main]

/-- The mixed descendant--ancestor step is derived from primitive virtual
cotangent, diagonal and stabilization laws. Both factors are actual GW values. -/
theorem mixed_step (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g (Option S)) (beta : B)
    (m : ℕ) (d : S → ℕ) (e : Option S → ℕ) (y : V) (a : S → V) :
    M.mixedInvariant P I g (Option S) h beta (Option.casesOn · (m+1) d) e
        (Option.casesOn · y a) =
      M.mixedInvariant P I g (Option S) h beta (Option.casesOn · m d)
          (Option.casesOn · (e none + 1) (fun s ↦ e (some s))) (Option.casesOn · y a) +
        ∑ split : ↥(D.positiveTailSplittings beta),
          M.mixedInvariant P I g (Option S) h split.val.1 (Option.casesOn · 0 d) e
            (Option.casesOn · (U.calibrationCoefficient (m+1) split.val.2 y) a) := by
  apply sub_eq_iff_eq_add'.mp
  rw [T.mixedInvariant_eq_integral, T.mixedInvariant_eq_integral, ← map_sub]
  have hmon : P.monomial g (Option S) h
      (Option.casesOn · (e none + 1) (fun s ↦ e (some s))) =
      P.monomial g (Option S) h e * P.psi g (Option S) h none := by
    simp only [PsiClasses.monomial, Fintype.prod_option, pow_succ]
    ring
  have hdesc : G.integrand g (Option S) beta (Option.casesOn · (m+1) d)
      (Option.casesOn · y a) =
      G.integrand g (Option S) beta (Option.casesOn · m d) (Option.casesOn · y a) *
        G.psi g (Option S) beta none := by
    simp only [StableMapIntersection.integrand, Fintype.prod_option, pow_succ]
    ring
  rw [hmon, map_mul, hdesc]
  have heq :
      G.integrand g (Option S) beta (Option.casesOn · m d) (Option.casesOn · y a) *
          G.psi g (Option S) beta none * T.pull g (Option S) h beta (P.monomial g (Option S) h e) -
        G.integrand g (Option S) beta (Option.casesOn · m d) (Option.casesOn · y a) *
          (T.pull g (Option S) h beta (P.monomial g (Option S) h e) *
            T.pull g (Option S) h beta (P.psi g (Option S) h none)) =
      (G.integrand g (Option S) beta (Option.casesOn · m d) (Option.casesOn · y a) *
          T.pull g (Option S) h beta (P.monomial g (Option S) h e)) *
        (G.psi g (Option S) beta none -
          T.pull g (Option S) h beta (P.psi g (Option S) h none)) := by ring
  rw [heq, K.cotangent]
  apply Finset.sum_congr rfl
  intro split _
  exact K.integrated_tail g S h beta split m d e y a

/-- Degree zero has no positive rational tails. Only transfer to the ancestor remains. -/
theorem mixed_step_zero_class (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g (Option S))
    (m : ℕ) (d : S → ℕ) (e : Option S → ℕ) (y : V) (a : S → V) :
    M.mixedInvariant P I g (Option S) h 0 (Option.casesOn · (m+1) d) e
        (Option.casesOn · y a) =
      M.mixedInvariant P I g (Option S) h 0 (Option.casesOn · m d)
        (Option.casesOn · (e none + 1) (fun s ↦ e (some s))) (Option.casesOn · y a) := by
  classical
  have hz : D.positiveTailSplittings 0 = ∅ := by
    rw [EffectiveCurveMonoid.positiveTailSplittings, D.splittings_zero]
    simp only [ne_eq, not_true_eq_false, Finset.filter_singleton, if_false]
  haveI : IsEmpty ↥(D.positiveTailSplittings 0) := by rw [hz]; infer_instance
  simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using
    K.mixed_step g S h 0 m d e y a

/-- On the three-point rational curve the ancestor term vanishes by dimension.
This derives actual stable-map recursion, retaining all other descendant powers. -/
theorem genusZero_threePoint (K : RationalTailIntersection G T P) (beta : B)
    (m : ℕ) (d : Fin 2 → ℕ) (y : V) (a : Fin 2 → V) :
    U.invariant 0 (Option (Fin 2)) beta (Option.casesOn · (m+1) d)
        (Option.casesOn · y a) =
      ∑ split : ↥(D.positiveTailSplittings beta),
        U.invariant 0 (Option (Fin 2)) split.val.1 (Option.casesOn · 0 d)
          (Option.casesOn · (U.calibrationCoefficient (m+1) split.val.2 y) a) := by
  have hp : P.psi 0 (Option (Fin 2)) StableArity.zero_option_fin_two none = 0 := by
    apply C.eq_zero_of_dimension_lt 0 (Option (Fin 2)) StableArity.zero_option_fin_two
      1 _ (P.psi_degree _ _ _ _)
    norm_num [StableArity.dimension]
  have hz : P.monomial 0 (Option (Fin 2)) StableArity.zero_option_fin_two
      (Option.casesOn · 1 (fun _ ↦ 0)) = 0 := by
    simp only [PsiClasses.monomial, Fintype.prod_option, hp, pow_one, pow_zero,
      Finset.prod_const_one, zero_mul]
  have he := K.mixed_step 0 (Fin 2) StableArity.zero_option_fin_two beta m d 0 y a
  simp only [Pi.zero_apply, zero_add] at he
  rw [M.mixedInvariant_zero_ancestor] at he
  have hfirst : M.mixedInvariant P I 0 (Option (Fin 2)) StableArity.zero_option_fin_two beta
      (Option.casesOn · m d) (Option.casesOn · 1 (fun _ ↦ 0)) (Option.casesOn · y a) = 0 := by
    rw [StableMapDescendants.mixedInvariant_apply, hz, mul_zero, map_zero]
  rw [hfirst, zero_add] at he
  simpa only [M.mixedInvariant_zero_ancestor, U.invariant_of_stable,
    StableArity.zero_option_fin_two] using he

/-- Every geometric tail has strictly smaller main-component energy. -/
theorem main_energy_lt (beta : B) (split : ↥(D.positiveTailSplittings beta)) :
    D.energy split.val.1 < D.energy beta := by
  have hs := (D.mem_positiveTailSplittings _ _ _).mp split.property
  have he := congrArg D.energy hs.1
  rw [map_add] at he
  have hp : 0 < D.energy split.val.2 :=
    Nat.pos_of_ne_zero ((D.energy_eq_zero_iff _).not.mpr hs.2)
  calc
    D.energy split.val.1 < D.energy split.val.1 + D.energy split.val.2 :=
      Nat.lt_add_of_pos_right hp
    _ = D.energy beta := he

/-- Moving a descendant power to its ancestor lowers the number of remaining
stable-map powers, independently of the curve class and ancestor exponents. -/
theorem shifted_descendant_degree_lt {S : Type} [Fintype S] (m : ℕ) (d : S → ℕ) :
    (∑ s : Option S, (Option.casesOn s m d : ℕ)) <
      ∑ s : Option S, Option.casesOn s (m+1) d := by
  simp only [Fintype.sum_option]
  omega

/-- The main factor loses the entire distinguished descendant power. -/
theorem main_descendant_degree_lt {S : Type} [Fintype S] (m : ℕ) (d : S → ℕ) :
    (∑ s : Option S, (Option.casesOn s 0 d : ℕ)) <
      ∑ s : Option S, Option.casesOn s (m+1) d := by
  simp only [Fintype.sum_option]
  omega

/-- The retained tail power is also strictly below the original total. -/
theorem tail_descendant_degree_lt {S : Type} [Fintype S] (m : ℕ) (d : S → ℕ) :
    m < ∑ s : Option S, Option.casesOn s (m+1) d := by
  simp only [Fintype.sum_option]
  omega

end RationalTailIntersection
end AxiomaticGW
