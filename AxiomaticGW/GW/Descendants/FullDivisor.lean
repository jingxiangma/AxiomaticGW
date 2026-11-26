/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.FullPotential

/-!
# Divisor equations across unstable curve arities

The optional numerical extension reuses the existing stable divisor law.
At degree zero its exceptional terms are the actual integrated genus-zero
three-point invariant and a supplied genus-one one-point linear functional.
No identification of the three-point invariant with a separately specified
cup product is assumed. The unstable recurrence remains explicit geometric
input, including at positive curve degree.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Exceptional divisor contribution for the zero convention on degree-zero
unstable numerical invariants. The genus-zero term uses the existing stable
three-point invariant; the genus-one term is supplied target data. -/
noncomputable def divisorCorrection
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
    (genusOneDivisor : Omega.graded.degree 1 →ₗ[R] R)
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ) (a : S → V)
    (divisorState : Omega.graded.degree 1) : R := by
  classical
  exact if h : g = 0 ∧ beta = 0 ∧ Fintype.card S = 2 ∧ (∀ s, k s = 0) then
    M.invariant I 0 (Option S)
      (by simp only [StableArity, Fintype.card_option, h.2.2.1]; omega)
      0 (fun _ ↦ 0) (fun | none => divisorState.1 | some s => a s)
  else dilatonCorrection (genusOneDivisor divisorState) g S beta

section Correction

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  (M : StableMapDescendants Omega) (I : StableCurveIntegration C)
  (genusOneDivisor : Omega.graded.degree 1 →ₗ[R] R)

/-- Exceptional divisor terms vanish on stable base arities. -/
theorem divisorCorrection_eq_zero_of_stable
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ) (a : S → V)
    (divisorState : Omega.graded.degree 1) (h : StableArity g S) :
    divisorCorrection M I genusOneDivisor g S beta k a divisorState = 0 := by
  classical
  unfold divisorCorrection
  split_ifs with hex
  · unfold StableArity at h
    rcases hex with ⟨rfl, _, hc, _⟩
    omega
  · exact dilatonCorrection_eq_zero_of_stable _ g S beta h

/-- Positive curve classes have no exceptional divisor contribution. -/
theorem divisorCorrection_eq_zero_of_ne_zero
    (g : ℕ) (S : Type) [Fintype S] (beta : B) (k : S → ℕ) (a : S → V)
    (divisorState : Omega.graded.degree 1) (h : beta ≠ 0) :
    divisorCorrection M I genusOneDivisor g S beta k a divisorState = 0 := by
  simp only [divisorCorrection, h, false_and, and_false, ↓reduceDIte]
  exact dilatonCorrection_eq_zero_of_ne_zero _ g S beta h

/-- At the genus-zero exceptional arity the correction is the existing
integrated three-point invariant with a divisor insertion. -/
theorem divisorCorrection_zero_fin_two
    (a : Fin 2 → V) (divisorState : Omega.graded.degree 1) :
    divisorCorrection M I genusOneDivisor 0 (Fin 2) 0 (fun _ ↦ 0) a divisorState =
      M.invariant I 0 (Option (Fin 2)) StableArity.zero_option_fin_two 0
        (fun _ ↦ 0) (fun | none => divisorState.1 | some s => a s) := by
  simp only [divisorCorrection, Fintype.card_fin, implies_true, and_self,
    ↓reduceDIte]
  congr 1
  funext x
  cases x <;> rfl

/-- The genus-one exceptional correction is the supplied linear functional
evaluated on the divisor state. -/
theorem divisorCorrection_one_empty
    (k : Empty → ℕ) (a : Empty → V) (divisorState : Omega.graded.degree 1) :
    divisorCorrection M I genusOneDivisor 1 Empty 0 k a divisorState =
      genusOneDivisor divisorState := by
  simp only [divisorCorrection, one_ne_zero, false_and, ↓reduceDIte,
    dilatonCorrection_one_empty]

end Correction

/-- Optional geometric divisor input for the numerical unstable extension.
The stable law and its divisor action are reused without modification. The
new recurrence is required only when the base curve arity is unstable. -/
structure FullDescendantDivisorLaw
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
    {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    (L : DescendantDivisorLaw M I A) where
  /-- Target-dependent degree-zero genus-one one-point divisor invariant. -/
  genusOneDivisor : Omega.graded.degree 1 →ₗ[R] R
  /-- The divisor recurrence at unstable base arities, with its exceptional
  degree-zero terms. This is additional geometric input, not a consequence of
  the numerical carrier or the stable divisor law. -/
  divisor_unstable : ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
      (_h : ¬StableArity g S) (beta : B) (k : S → ℕ) (a : S → V)
      (divisorState : Omega.graded.degree 1),
    U.invariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => divisorState.1 | some s => a s) =
      A.divisorPairing divisorState beta * U.invariant g S beta k a +
        (∑ s, if k s = 0 then 0 else
          U.invariant g S beta (lowerPower k s)
            (replaceInput a s (L.divisorAction divisorState (a s)))) +
        divisorCorrection M I genusOneDivisor g S beta k a divisorState

namespace FullDescendantDivisorLaw

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {Omega : GromovWittenTheory R V B D C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  {U : UnstableDescendantConventions M I}
  {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
  {L : DescendantDivisorLaw M I A}

/-- The corrected all-arity divisor equation follows from the stable law and
the separately supplied unstable geometric recurrence. -/
theorem global_divisor (H : FullDescendantDivisorLaw U L)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (beta : B) (k : S → ℕ) (a : S → V)
    (divisorState : Omega.graded.degree 1) :
    U.invariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => divisorState.1 | some s => a s) =
      A.divisorPairing divisorState beta * U.invariant g S beta k a +
        (∑ s, if k s = 0 then 0 else
          U.invariant g S beta (lowerPower k s)
            (replaceInput a s (L.divisorAction divisorState (a s)))) +
        divisorCorrection M I H.genusOneDivisor g S beta k a divisorState := by
  by_cases h : StableArity g S
  · rw [divisorCorrection_eq_zero_of_stable M I H.genusOneDivisor
        g S beta k a divisorState h, add_zero,
      U.invariant_of_stable g (Option S) (StableArity.option h),
      U.invariant_of_stable g S h]
    refine (L.divisor g S h beta k a divisorState).trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro s _hs
    split_ifs
    · rfl
    · rw [U.invariant_of_stable g S h]
  · exact H.divisor_unstable g S h beta k a divisorState

/-- At positive curve degree the ordinary divisor equation holds at every
curve arity, including those that are unstable after forgetting the divisor. -/
theorem global_divisor_of_ne_zero (H : FullDescendantDivisorLaw U L)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (beta : B) (k : S → ℕ) (a : S → V)
    (divisorState : Omega.graded.degree 1) (hbeta : beta ≠ 0) :
    U.invariant g (Option S) beta
        (fun | none => 0 | some s => k s)
        (fun | none => divisorState.1 | some s => a s) =
      A.divisorPairing divisorState beta * U.invariant g S beta k a +
        ∑ s, if k s = 0 then 0 else
          U.invariant g S beta (lowerPower k s)
            (replaceInput a s (L.divisorAction divisorState (a s))) := by
  simpa only [divisorCorrection_eq_zero_of_ne_zero M I H.genusOneDivisor
    g S beta k a divisorState hbeta, add_zero]
      using H.global_divisor g S beta k a divisorState

end FullDescendantDivisorLaw

end AxiomaticGW
