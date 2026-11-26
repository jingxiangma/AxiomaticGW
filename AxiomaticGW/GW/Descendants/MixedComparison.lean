/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Geometry.RationalTailComparison
public import Mathlib.Logic.Equiv.Option

/-!
# Cotangent comparison at any retained marking

The virtual rational-tail formula is transported from its distinguished
`Option.none` marking to an arbitrary finite marking set. Both cotangent
families and every state move together. The replacement node retains its
ancestor exponent and has zero stable-map descendant exponent.
-/

@[expose] public section

namespace AxiomaticGW
namespace RationalTailIntersection

private theorem update_comp_optionSubtypeNe {S W : Type*} [DecidableEq S]
    (s : S) (f : S → W) (w : W) :
    Function.update f s w ∘ Equiv.optionSubtypeNe s =
      (Option.casesOn · w (fun t : {t : S // t ≠ s} ↦ f t)) := by
  funext t
  cases t with
  | none => exact Function.update_self s w f
  | some t => exact Function.update_of_ne t.property w f

private theorem comp_optionSubtypeNe {S W : Type*} [DecidableEq S]
    (s : S) (f : S → W) :
    f ∘ Equiv.optionSubtypeNe s =
      (Option.casesOn · (f s) (fun t : {t : S // t ≠ s} ↦ f t)) := by
  funext t
  cases t <;> rfl

universe u
variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {T : StableMapStabilization G} {P : PsiClasses C}

/-- The geometric mixed step at any selected retained marking. -/
theorem mixed_step_at (K : RationalTailIntersection G T P)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S)
    (s : S) (beta : B) (m : ℕ) (d e : S → ℕ) (a : S → V) :
    M.mixedInvariant P I g S h beta (Function.update d s (m+1)) e a =
      M.mixedInvariant P I g S h beta (Function.update d s m)
          (Function.update e s (e s + 1)) a +
        ∑ split : ↥(D.positiveTailSplittings beta),
          M.mixedInvariant P I g S h split.val.1 (Function.update d s 0) e
            (Function.update a s (U.calibrationCoefficient (m+1) split.val.2 (a s))) := by
  let b := Equiv.optionSubtypeNe s
  have h' : StableArity g (Option {t : S // t ≠ s}) := by
    simpa only [StableArity, Fintype.card_congr b] using h
  have hr (c : B) (d' e' : S → ℕ) (a' : S → V) :=
    M.mixedInvariant_relabel_apply P I g _ S h' h b c d' e' a'
  rw [← hr beta (Function.update d s (m+1)) e a,
    ← hr beta (Function.update d s m) (Function.update e s (e s + 1)) a]
  simp only [b, update_comp_optionSubtypeNe]
  simp only [comp_optionSubtypeNe]
  rw [K.mixed_step]
  congr 1
  apply Finset.sum_congr rfl
  intro split _
  rw [← hr split.val.1 (Function.update d s 0) e
    (Function.update a s (U.calibrationCoefficient (m+1) split.val.2 (a s)))]
  simp only [b, update_comp_optionSubtypeNe]
  simp only [comp_optionSubtypeNe]

end RationalTailIntersection
end AxiomaticGW
