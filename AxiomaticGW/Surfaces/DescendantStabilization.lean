/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.DescendantDivisor

/-!
# Anticanonical reduction of unstable descendant arities

For the three fixed surfaces, a positive effective class has positive
anticanonical degree. Solving the existing divisor equation therefore
expresses any invariant as the invariant with one primary anticanonical
insertion minus terms with a lower cotangent power, divided by that degree.

At curve-unstable arity every resulting request decreases the sum of total
cotangent power and the arity deficit. Thus stable-arity descendant values
determine all positive-degree unstable values; they introduce no independent
infinite seed family. Stable-arity reconstruction and descendant--ancestor
comparison remain separate requirements.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceCohomology

/-- The anticanonical divisor meets a hyperplane in three points. -/
theorem firstChern_mul_hyperplane (r : ℕ) :
    (firstChernDivisor r).val * hyperplane r = (3 : ℚ) • point r := by
  rw [mul_comm, firstChernDivisor, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_sum]
  simp only [hyperplaneDivisor, exceptionalDivisor, mul_sub, mul_smul_comm,
    hyperplane_mul_hyperplane, Finset.mul_sum, hyperplane_mul_exceptional,
    Finset.sum_const_zero, sub_zero]

/-- The exceptional self-intersection sign gives a positive anticanonical product. -/
theorem firstChern_mul_exceptional (r : ℕ) (i : Fin r) :
    (firstChernDivisor r).val * exceptional r i = point r := by
  have hh : exceptional r i * hyperplane r = 0 :=
    (mul_comm _ _).trans (hyperplane_mul_exceptional r i)
  rw [mul_comm, firstChernDivisor, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_sum]
  simp only [hyperplaneDivisor, exceptionalDivisor, mul_sub, mul_smul_comm,
    hh, smul_zero, Finset.mul_sum, exceptional_mul_exceptional,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_sub, neg_neg]

/-- A divisor times the top-degree point class vanishes. -/
theorem firstChern_mul_point (r : ℕ) :
    (firstChernDivisor r).val * point r = 0 := by
  rw [mul_comm, firstChernDivisor, Submodule.coe_sub, Submodule.coe_smul,
    Submodule.coe_sum]
  simp only [hyperplaneDivisor, exceptionalDivisor, mul_sub, mul_smul_comm,
    point_mul_hyperplane, smul_zero, Finset.mul_sum, point_mul_exceptional,
    Finset.sum_const_zero, sub_zero]

end SurfaceCohomology

namespace SurfaceDescendant

open SurfaceCohomology

/-- Lowering a positive cotangent power strictly reduces their total. -/
theorem totalPsi_lowerPower_lt {S : Type} [Fintype S] [DecidableEq S]
    (k : S → ℕ) (s : S) (hs : 0 < k s) :
    (∑ t, lowerPower k s t) < ∑ t, k t := by
  apply Finset.sum_lt_sum
  · intro t _
    by_cases h : t = s
    · subst t
      simp only [lowerPower, Function.update_self]
      omega
    · simp only [lowerPower, Function.update_of_ne h, le_refl]
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    simp only [lowerPower, Function.update_self]
    omega

/-- Adding a marking strictly reduces an unstable curve arity deficit. -/
theorem arityDeficit_option_lt (g : ℕ) (S : Type) [Fintype S]
    (h : ¬StableArity g S) :
    3 - (2 * g + Fintype.card (Option S)) < 3 - (2 * g + Fintype.card S) := by
  simp only [Fintype.card_option]
  unfold StableArity at h
  omega

/-- Number of cotangent powers plus missing markings for curve stability. -/
def stabilizationComplexity (g : ℕ) (S : Type) [Fintype S] (k : S → ℕ) : ℕ :=
  (∑ s, k s) + (3 - (2 * g + Fintype.card S))

/-- The added primary divisor preserves total psi degree and improves stability. -/
theorem stabilizationComplexity_option_lt (g : ℕ) (S : Type) [Fintype S]
    (k : S → ℕ) (h : ¬StableArity g S) :
    stabilizationComplexity g (Option S) (Option.elim · 0 k) <
      stabilizationComplexity g S k := by
  simp only [stabilizationComplexity, Fintype.sum_option,
    Option.elim_none, Option.elim_some, zero_add]
  exact Nat.add_lt_add_left (arityDeficit_option_lt g S h) _

/-- Every correction term strictly lowers total psi degree at fixed arity. -/
theorem stabilizationComplexity_lowerPower_lt (g : ℕ) (S : Type)
    [Fintype S] [DecidableEq S] (k : S → ℕ) (s : S) (hs : 0 < k s) :
    stabilizationComplexity g S (lowerPower k s) < stabilizationComplexity g S k :=
  Nat.add_lt_add_right (totalPsi_lowerPower_lt k s hs) _

/-- Solve the original positive-degree divisor equation using the anticanonical
class. Its coefficient is the nonzero full curve energy; the correction uses
the cup product proved from the existing laws. -/
theorem invariant_eq_anticanonical {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (beta : X.Curve) (hb : beta ≠ 0) (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    U.invariant g S beta k a =
      (U.invariant g (Option S) beta (Option.elim · 0 k)
        (Option.elim · (firstChernDivisor X.blowups).val a) -
        ∑ s, if k s = 0 then 0 else
          U.invariant g S beta (lowerPower k s)
            (replaceInput a s ((firstChernDivisor X.blowups).val * a s))) /
        (X.effective.energy beta : ℚ) := by
  have hc : A.divisorPairing (T.divisor (firstChernDivisor X.blowups)) beta =
      (X.effective.energy beta : ℚ) := by
    rw [hpair, SurfaceTarget.divisorPairing_firstChernDivisor]
    change ((X.effective.energy beta : ℤ) : ℚ) = _
    exact Int.cast_natCast _
  have hn : (X.effective.energy beta : ℚ) ≠ 0 := by
    exact_mod_cast (X.effective.energy_eq_zero_iff beta).not.mpr hb
  have he := H.global_divisor_of_ne_zero g S beta k a
    (T.divisor (firstChernDivisor X.blowups)) hb
  rw [hc] at he
  simp only [T.divisorAction_eq_mul U laws L, SurfaceTheoryIdentification.divisor] at he
  apply (eq_div_iff hn).mpr
  rw [mul_comm]
  apply (eq_sub_iff_add_eq).mpr
  refine he.symm.trans ?_
  congr 1
  · funext t
    cases t <;> rfl
  · funext t
    cases t <;> rfl

/-- Internal fuel-based reduction; use `stabilizedValue` for its proved sufficient bound.
The supplied
values are defined only at stable curve arities. The zero-fuel fallback is
unreachable once the bound dominates `stabilizationComplexity`, as proved below. -/
def stabilizeAux (X : SurfaceTarget) (g : ℕ) (beta : X.Curve)
    (stableValues : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity g S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ) :
    ℕ → (S : Type) → [Fintype S] → [DecidableEq S] →
      (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ
  | fuel, S, _, _, k, a =>
      letI : Decidable (StableArity g S) :=
        inferInstanceAs (Decidable (2 < 2 * g + Fintype.card S))
      if h : StableArity g S then stableValues S h k a
      else if beta = 0 then 0
      else match fuel with
      | 0 => 0
      | n + 1 =>
          (stabilizeAux X g beta stableValues n (Option S) (Option.elim · 0 k)
            (Option.elim · (firstChernDivisor X.blowups).val a) -
            ∑ s, if k s = 0 then 0 else
              stabilizeAux X g beta stableValues n S (lowerPower k s)
                (replaceInput a s ((firstChernDivisor X.blowups).val * a s))) /
            (X.effective.energy beta : ℚ)

/-- A sufficient, explicitly computed recursion bound for every finite request. -/
def stabilizedValue (X : SurfaceTarget) (g : ℕ) (beta : X.Curve)
    (stableValues : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity g S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (S : Type) [Fintype S] [DecidableEq S] (k : S → ℕ)
    (a : S → SurfaceCohomology X.blowups) : ℚ :=
  stabilizeAux X g beta stableValues (stabilizationComplexity g S k) S k a

/-- Apply the stable-arity adapter to an existing full-class query, preserving
its geometric-domain check. The callback is still required to supply correct
stable descendants; this function does not reconstruct those values itself. -/
def stabilizedQuery? (X : SurfaceTarget) (q : SurfaceQuery X)
    (stableValues : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity q.genus S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ) : Option ℚ :=
  if q.GeometricDomain then
    some (stabilizedValue X q.genus q.beta stableValues (Fin q.insertions.length)
      (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label.value))
  else none

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {I : StableCurveIntegration C} {F : ForgetfulPushforward C I}
  {A : GWDivisorAxiom Omega F}

/-- A sufficient fuel bound computes the original numerical invariant from
correct stable-arity values. This is an adapter for stable reconstruction,
not an assumption that those stable values are already known. -/
private theorem stabilizeAux_eq_invariant {M : StableMapDescendants Omega}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I) {L : DescendantDivisorLaw M I A}
    (H : FullDescendantDivisorLaw U L) (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (beta : X.Curve)
    (stableValues : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity g S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (hstable : ∀ (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      stableValues S h k a = M.invariant I g S h beta k a)
    (fuel : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups)
    (hbound : stabilizationComplexity g S k ≤ fuel) :
    stabilizeAux X g beta stableValues fuel S k a = U.invariant g S beta k a := by
  induction fuel generalizing S with
  | zero =>
      by_cases hs : StableArity g S
      · rw [stabilizeAux, dif_pos hs, U.invariant_of_stable g S hs]
        exact hstable S hs k a
      · have hc : 0 < 3 - (2 * g + Fintype.card S) := by
          unfold StableArity at hs
          omega
        unfold stabilizationComplexity at hbound
        omega
  | succ fuel ih =>
      by_cases hs : StableArity g S
      · rw [stabilizeAux, dif_pos hs, U.invariant_of_stable g S hs]
        exact hstable S hs k a
      · by_cases hb : beta = 0
        · subst beta
          rw [stabilizeAux, dif_neg hs, if_pos rfl,
            U.invariant_of_unstable g S hs, U.unstable_zero g S hs]
          rfl
        · rw [stabilizeAux, dif_neg hs, if_neg hb]
          have hadd := ih (Option S) (Option.elim · 0 k)
            (Option.elim · (firstChernDivisor X.blowups).val a)
            (by have := stabilizationComplexity_option_lt g S k hs; omega)
          have hsum :
              (∑ s, if k s = 0 then 0 else
                stabilizeAux X g beta stableValues fuel S (lowerPower k s)
                  (replaceInput a s ((firstChernDivisor X.blowups).val * a s))) =
              ∑ s, if k s = 0 then 0 else U.invariant g S beta (lowerPower k s)
                (replaceInput a s ((firstChernDivisor X.blowups).val * a s)) := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases hk : k s = 0
            · rw [if_pos hk, if_pos hk]
            · rw [if_neg hk, if_neg hk]
              apply ih
              have := stabilizationComplexity_lowerPower_lt g S k s (Nat.pos_of_ne_zero hk)
              omega
          rw [hadd, hsum]
          exact (invariant_eq_anticanonical U T laws H hpair g S beta hb k a).symm

/-- The executable bound always suffices; no exhausted branch supplies a value. -/
theorem stabilizedValue_eq_invariant {M : StableMapDescendants Omega}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I) {L : DescendantDivisorLaw M I A}
    (H : FullDescendantDivisorLaw U L) (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (beta : X.Curve)
    (stableValues : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity g S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (hstable : ∀ (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      stableValues S h k a = M.invariant I g S h beta k a)
    (S : Type) [Fintype S] [DecidableEq S] (k : S → ℕ)
    (a : S → SurfaceCohomology X.blowups) :
    stabilizedValue X g beta stableValues S k a = U.invariant g S beta k a :=
  stabilizeAux_eq_invariant U T laws H hpair g beta stableValues hstable
    _ S k a le_rfl

/-- Agreement at stable arity propagates to every arity at the same full class,
using the proved terminating evaluator. Degree-zero unstable requests use the
original zero convention; no extra unstable values are assumed. -/
theorem invariant_eq_of_stable_eq
    {M₁ M₂ : StableMapDescendants Omega}
    (U₁ : UnstableDescendantConventions M₁ I) (U₂ : UnstableDescendantConventions M₂ I)
    (T : SurfaceTheoryIdentification X Omega)
    (laws₁ : DescendantStringDilatonLaws M₁ I) (laws₂ : DescendantStringDilatonLaws M₂ I)
    {L₁ : DescendantDivisorLaw M₁ I A} {L₂ : DescendantDivisorLaw M₂ I A}
    (H₁ : FullDescendantDivisorLaw U₁ L₁) (H₂ : FullDescendantDivisorLaw U₂ L₂)
    (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (beta : X.Curve)
    (hstable : ∀ (S : Type) [Fintype S] (h : StableArity g S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      M₁.invariant I g S h beta k a = M₂.invariant I g S h beta k a)
    (S : Type) [Fintype S] (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    U₁.invariant g S beta k a = U₂.invariant g S beta k a := by
  classical
  let v (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) : ℚ :=
    M₁.invariant I g S h beta k a
  have h₁ := stabilizedValue_eq_invariant U₁ T laws₁ H₁ hpair g beta v
    (fun _ _ _ _ _ _ ↦ rfl) S k a
  have h₂ := stabilizedValue_eq_invariant U₂ T laws₂ H₂ hpair g beta v
    (fun S _ _ h k a ↦ hstable S h k a) S k a
  exact h₁.symm.trans h₂

/-- A fixed stable descendant family has at most one full numerical extension
satisfying the existing surface divisor and string laws. At degree-zero
unstable arity this uses the original auxiliary zero convention. -/
theorem numerical_extension_unique {M : StableMapDescendants Omega}
    (U₁ U₂ : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {L₁ L₂ : DescendantDivisorLaw M I A}
    (H₁ : FullDescendantDivisorLaw U₁ L₁) (H₂ : FullDescendantDivisorLaw U₂ L₂)
    (hpair : T.DivisorPairingCompatible A)
    (g : ℕ) (S : Type) [Fintype S] (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    U₁.invariant g S beta k a = U₂.invariant g S beta k a := by
  exact invariant_eq_of_stable_eq U₁ U₂ T laws laws H₁ H₂ hpair g beta
    (fun _ _ _ _ _ ↦ rfl) S k a

/-- Query evaluation agrees with the original descendant interface, including
rejection of auxiliary degree-zero unstable requests. -/
theorem stabilizedQuery?_eq_checkedEval {M : StableMapDescendants Omega}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I) {L : DescendantDivisorLaw M I A}
    (H : FullDescendantDivisorLaw U L) (hpair : T.DivisorPairingCompatible A)
    (q : SurfaceQuery X)
    (stableValues : ∀ (S : Type) [Fintype S] [DecidableEq S],
      StableArity q.genus S → (S → ℕ) → (S → SurfaceCohomology X.blowups) → ℚ)
    (hstable : ∀ (S : Type) [Fintype S] [DecidableEq S] (h : StableArity q.genus S)
      (k : S → ℕ) (a : S → SurfaceCohomology X.blowups),
      stableValues S h k a = M.invariant I q.genus S h q.beta k a) :
    stabilizedQuery? X q stableValues = q.checkedEval U := by
  unfold stabilizedQuery? SurfaceQuery.checkedEval
  split_ifs
  · congr 1
    exact stabilizedValue_eq_invariant U T laws H hpair q.genus q.beta stableValues hstable
      (Fin q.insertions.length) _ _
  · rfl

end SurfaceDescendant
end AxiomaticGW
