/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GW.Descendants.CalibrationRecursion

set_option linter.privateModule false

namespace AxiomaticGWTest.GW.MixedComparison
open AxiomaticGW

variable {R V B : Type} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {St : StableMapStabilization G} {P : PsiClasses C}

/-- The two mixed endpoints are different existing families. -/
example (g S) [Fintype S] (h : StableArity g S) (beta : B) (k : S → ℕ) :
    M.mixedInvariant P I g S h beta k 0 = M.invariant I g S h beta k ∧
    M.mixedInvariant P I g S h beta 0 k = Omega.ancestorInvariant P I g S h beta k :=
  ⟨M.mixedInvariant_zero_ancestor P I g S h beta k,
    M.mixedInvariant_zero_descendant P I g S h beta k⟩

/-- Both power families and all states must move with a change of marking frame. -/
example (g S T) [Fintype S] [Fintype T] (hS : StableArity g S) (hT : StableArity g T)
    (b : S ≃ T) (beta : B) (d e : T → ℕ) (a : T → V) :
    M.mixedInvariant P I g S hS beta (d ∘ b) (e ∘ b) (a ∘ b) =
      M.mixedInvariant P I g T hT beta d e a :=
  M.mixedInvariant_relabel_apply P I g S T hS hT b beta d e a

/-- Zero-class comparison has no invented degree-zero two-point metric term. -/
example (K : RationalTailIntersection G St P) (g S) [Fintype S]
    (h : StableArity g (Option S)) (m : ℕ) (d : S → ℕ) (e : Option S → ℕ)
    (y : V) (a : S → V) :
    M.mixedInvariant P I g (Option S) h 0 (Option.casesOn · (m+1) d) e
        (Option.casesOn · y a) =
      M.mixedInvariant P I g (Option S) h 0 (Option.casesOn · m d)
        (Option.casesOn · (e none + 1) (fun s ↦ e (some s))) (Option.casesOn · y a) :=
  K.mixed_step_zero_class g S h m d e y a

/-- A genus-two main component retains its node ancestor exponent. -/
example (K : RationalTailIntersection G St P) (beta : B)
    (split : ↥(D.positiveTailSplittings beta)) (m : ℕ) (e : Option Empty → ℕ) (y : V) :
    K.integrate 2 Empty (by norm_num [StableArity]) beta split
      (K.pull 2 Empty (by norm_num [StableArity]) beta split
        (G.integrand 2 (Option Empty) beta (Option.casesOn · m Empty.elim)
          (Option.casesOn · y Empty.elim) * St.pull 2 (Option Empty)
            (by norm_num [StableArity]) beta (P.monomial 2 (Option Empty)
              (by norm_num [StableArity]) e))) =
      M.mixedInvariant P I 2 (Option Empty) (by norm_num [StableArity]) split.val.1
        (Option.casesOn · 0 Empty.elim) e
        (Option.casesOn · (U.calibrationCoefficient (m+1) split.val.2 y) Empty.elim) :=
  K.integrated_tail 2 Empty _ beta split m Empty.elim e y Empty.elim

/-- Every main term has genuinely smaller effective energy. -/
example (beta : B) (split : ↥(D.positiveTailSplittings beta)) :
    D.energy split.val.1 < D.energy beta := RationalTailIntersection.main_energy_lt beta split

/-- All three recursive descendant measures decrease. -/
example (m : ℕ) (d : Fin 3 → ℕ) :
    (∑ s : Option (Fin 3), (Option.casesOn s m d : ℕ)) <
      (∑ s : Option (Fin 3), Option.casesOn s (m+1) d) ∧
    (∑ s : Option (Fin 3), (Option.casesOn s 0 d : ℕ)) <
      (∑ s : Option (Fin 3), Option.casesOn s (m+1) d) ∧
    m < (∑ s : Option (Fin 3), Option.casesOn s (m+1) d) :=
  ⟨RationalTailIntersection.shifted_descendant_degree_lt m d,
    RationalTailIntersection.main_descendant_degree_lt m d,
    RationalTailIntersection.tail_descendant_degree_lt m d⟩

end AxiomaticGWTest.GW.MixedComparison
