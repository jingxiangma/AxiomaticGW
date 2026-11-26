/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.FullPotential
public import Mathlib.Data.Fin.VecNotation

/-!
# The descendant divisor action is determined by primary invariants

Evaluate the degree-zero genus-zero invariant with insertions
`D, 1, tau_1(x), y` by the string and divisor equations. The first
calculation gives the primary cubic `D, x, y`; the second gives the
metric paired with `divisorAction D x`. Perfectness then determines
the action uniquely. No separate cup-product compatibility is assumed.

The full numerical string law is used only for its existing three-point
metric correction. The four-point string and divisor calculations use
the unchanged stable laws.
-/

@[expose] public section

namespace AxiomaticGW

universe u

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

namespace UnstableDescendantConventions

/-- The existing exceptional string correction fixes the primary unit cubic. -/
theorem primary_unit_pairing (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I) (x y : V) :
    U.invariant 0 (Option (Fin 2)) 0 (fun _ ↦ 0)
      (fun | none => Omega.unit | some s => ![x, y] s) = Omega.pairing.form x y := by
  have h := U.global_string S 0 (Fin 2) 0 (fun _ ↦ 0) ![x, y]
  simp only [stringCorrection, implies_true, and_self, ite_true, Finset.sum_const_zero, zero_add,
    twoPointPairing_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  convert! h using 1
  congr 1 <;> funext i <;> cases i <;> rfl

end UnstableDescendantConventions

namespace DescendantDivisorLaw

variable {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}

/-- String and divisor evaluate the same four-point invariant; their equality
identifies the divisor action through the primary cubic and the metric. -/
theorem divisorAction_pairing (L : DescendantDivisorLaw M I A)
    (U : UnstableDescendantConventions M I) (S : DescendantStringDilatonLaws M I)
    (d : Omega.graded.degree 1) (x y : V) :
    Omega.pairing.form (L.divisorAction d x) y =
      U.invariant 0 (Option (Fin 2)) 0 (fun _ ↦ 0) (fun | none => d.1 | some s => ![x, y] s) := by
  let k : Option (Fin 2) → ℕ := (fun | none => 0 | some s => ![1, 0] s)
  let a : Option (Fin 2) → V := (fun | none => Omega.unit | some s => ![x, y] s)
  let b : Option (Fin 2) → V := (fun | none => d.1 | some s => ![x, y] s)
  have hdiv := L.divisor 0 (Option (Fin 2)) StableArity.zero_option_fin_two 0 k a d
  simp only [map_zero, zero_mul, zero_add, Fintype.sum_option, Fin.sum_univ_two,
    k, Matrix.cons_val_zero, Matrix.cons_val_one,
    if_true, if_false, one_ne_zero, add_zero, zero_add] at hdiv
  have hlow : lowerPower k (some 0) = fun _ ↦ 0 := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  have hrep : replaceInput a (some 0) (L.divisorAction d x) =
      (fun | none => Omega.unit | some s => ![L.divisorAction d x, y] s) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  have ha0 : a (some 0) = x := rfl
  rw [hlow, ha0, hrep] at hdiv
  have hstr := S.string 0 (Option (Fin 2)) StableArity.zero_option_fin_two 0 k b
  simp only [Fintype.sum_option, Fin.sum_univ_two, k, Matrix.cons_val_zero, Matrix.cons_val_one,
    if_true, if_false, one_ne_zero, add_zero, zero_add] at hstr
  rw [hlow] at hstr
  have hrel := congrArg (fun f ↦ f (fun | none => Omega.unit | some s => b s))
    (M.invariant_relabel I 0 (Option (Option (Fin 2))) (Option (Option (Fin 2)))
      (StableArity.option StableArity.zero_option_fin_two)
      (StableArity.option StableArity.zero_option_fin_two)
      (swapDoubleOption (Fin 2)) 0 (fun | none => 0 | some s => k s))
  change M.invariant I 0 _ _ 0 (fun | none => 0 | some s => k s)
      (fun s ↦ (fun | none => Omega.unit | some s => b s) (swapDoubleOption (Fin 2) s)) =
    M.invariant I 0 _ _ 0
      (fun t ↦ (fun | none => 0 | some s => k s) ((swapDoubleOption (Fin 2)).symm t))
      (fun | none => Omega.unit | some s => b s) at hrel
  have ha : (fun s ↦ (fun | none => Omega.unit | some s => b s) (swapDoubleOption (Fin 2) s)) =
      (fun | none => d.1 | some s => a s) := by
    funext i
    rcases i with _ | (_ | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl
  have hk : (fun t ↦ (fun | none => 0 | some s => k s) ((swapDoubleOption (Fin 2)).symm t)) =
      (fun | none => 0 | some s => k s) := by
    funext i
    rcases i with _ | (_ | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl
  rw [ha, hk] at hrel
  simp only [k] at hrel
  have hdiv' : M.invariant I 0 (Option (Option (Fin 2)))
      (StableArity.option StableArity.zero_option_fin_two) 0
      (fun | none => 0 | some s => k s) (fun | none => d.1 | some s => a s) =
      M.invariant I 0 (Option (Fin 2)) StableArity.zero_option_fin_two 0
        (fun _ ↦ 0) (fun | none => Omega.unit | some s => ![L.divisorAction d x, y] s) := by
    convert! hdiv using 1
    congr 2 <;> funext i <;> cases i <;> rfl
  have hstr' : M.invariant I 0 (Option (Option (Fin 2)))
      (StableArity.option StableArity.zero_option_fin_two) 0
      (fun | none => 0 | some s => k s) (fun | none => Omega.unit | some s => b s) =
      M.invariant I 0 (Option (Fin 2)) StableArity.zero_option_fin_two 0
        (fun _ ↦ 0) b := by
    convert! hstr using 1
    congr 2 <;> funext i <;> cases i <;> rfl
  have hfinal := hdiv'.symm.trans (hrel.trans hstr')
  rw [← U.invariant_of_stable 0 (Option (Fin 2)) StableArity.zero_option_fin_two,
    ← U.invariant_of_stable 0 (Option (Fin 2)) StableArity.zero_option_fin_two,
    U.primary_unit_pairing S] at hfinal
  exact hfinal

/-- For a fixed descendant family satisfying string, the divisor action is unique. -/
theorem divisorAction_unique (L L' : DescendantDivisorLaw M I A)
    (U : UnstableDescendantConventions M I) (S : DescendantStringDilatonLaws M I) :
    L.divisorAction = L'.divisorAction := by
  ext d x
  apply Omega.pairing.toDual.injective
  ext y
  simp only [SymmetricPerfectPairing.toDual_apply]
  rw [L.divisorAction_pairing U S, L'.divisorAction_pairing U S]

end DescendantDivisorLaw
end AxiomaticGW
