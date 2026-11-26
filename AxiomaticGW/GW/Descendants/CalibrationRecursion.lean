/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Geometry.RationalTailComparison
public import AxiomaticGW.GW.Descendants.FullDivisor

/-!
# Deriving calibration recursion from cotangent geometry and the divisor law

The three-point rational ancestor term vanishes by dimension. Applying the
resulting stable-map relation to a primary divisor and a two-point descendant,
then using the original divisor equation, lowers the inverse-loop power.
The right side uses only primary three-point values, the previous calibration
power and the original divisor action. No new numerical recursion is assumed.
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

/-- Simultaneously transport powers and insertions into any finite label frame. -/
theorem invariant_relabel_comp (U : UnstableDescendantConventions M I)
    (g : ℕ) (S T : Type) [Fintype S] [Fintype T] (b : S ≃ T)
    (beta : B) (d : T → ℕ) (a : T → V) :
    U.invariant g S beta (d ∘ b) (a ∘ b) = U.invariant g T beta d a := by
  have h := congrArg (fun f ↦ f a) (U.invariant_relabel g S T b beta (d ∘ b))
  have hd : (fun t ↦ (d ∘ b) (b.symm t)) = d := by
    funext t
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  simp only [MultilinearMap.domDomCongr_apply, hd, U.invariantMap_apply] at h
  exact h

end UnstableDescendantConventions

namespace FullDescendantDivisorLaw

/-- At positive class, a primary three-point divisor insertion is the curve
intersection times the actual first calibration coefficient. -/
theorem primary_threePoint_calibration
    {U : UnstableDescendantConventions M I}
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (beta : B) (hb : beta ≠ 0) (divisor : Omega.graded.degree 1) (x y : V) :
    U.invariant 0 (Option (Fin 2)) beta 0 (Option.casesOn · y ![divisor.val,x]) =
      A.divisorPairing divisor beta * Omega.pairing.form x
        (U.calibrationCoefficient 1 beta y) := by
  have hd := H.global_divisor_of_ne_zero 0 (Fin 2) beta 0 ![x,y] divisor hb
  simp only [Pi.zero_apply, ↓reduceIte, Finset.sum_const_zero, add_zero] at hd
  rw [U.calibrationCoefficient_pairing]
  let b : Option (Fin 2) ≃ Option (Fin 2) :=
    (Equiv.swap none (some 1)).trans (Equiv.swap none (some 0))
  have hr := U.invariant_relabel_comp 0 _ _ b beta
    (fun | none => 0 | some s => (0 : Fin 2 → ℕ) s)
    (fun | none => divisor.val | some s => (![x,y] : Fin 2 → V) s)
  calc
    _ = U.invariant 0 (Option (Fin 2)) beta
        (fun | none => 0 | some s => (0 : Fin 2 → ℕ) s)
        (fun | none => divisor.val | some s => (![x,y] : Fin 2 → V) s) := by
      convert hr using 1
      congr 1 <;> funext i <;> rcases i with _ | i
      all_goals first | rfl | (fin_cases i <;> rfl)
    _ = _ := by
      convert hd using 1
      · congr 1 <;> funext i <;> cases i <;> rfl
      · congr 2
        funext i
        fin_cases i <;> rfl

end FullDescendantDivisorLaw

namespace RationalTailIntersection
variable {U : UnstableDescendantConventions M I} {G : StableMapIntersection U}
  {T : StableMapStabilization G} {P : PsiClasses C}

/-- A divisor inserted in the three-point rational recursion leaves only primary
main components, with the actual previous-power calibration state at their node. -/
theorem threePoint_divisor (K : RationalTailIntersection G T P) (beta : B)
    (m : ℕ) (divisor x y : V) :
    U.invariant 0 (Option (Fin 2)) beta (Option.casesOn · 0 (![0,m+1] : Fin 2 → ℕ))
        (Option.casesOn · divisor (![x,y] : Fin 2 → V)) =
      ∑ split : ↥(D.positiveTailSplittings beta),
        U.invariant 0 (Option (Fin 2)) split.val.1 0
          (Option.casesOn · (U.calibrationCoefficient (m+1) split.val.2 y) ![divisor,x]) := by
  let b : Option (Fin 2) ≃ Option (Fin 2) :=
    (Equiv.swap none (some 1)).trans (Equiv.swap none (some 0))
  have hk : (Option.casesOn · 0 (![0,m+1] : Fin 2 → ℕ) : Option (Fin 2) → ℕ) ∘ b =
      (Option.casesOn · (m+1) (fun _ : Fin 2 ↦ 0) : Option (Fin 2) → ℕ) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  have ha : (Option.casesOn · divisor (![x,y] : Fin 2 → V) : Option (Fin 2) → V) ∘ b =
      (Option.casesOn · y (![divisor,x] : Fin 2 → V) : Option (Fin 2) → V) := by
    funext i
    rcases i with _ | i
    · rfl
    · fin_cases i <;> rfl
  rw [← U.invariant_relabel_comp 0 _ _ b beta, hk, ha]
  refine (K.genusZero_threePoint beta m (fun _ ↦ 0) y ![divisor,x]).trans ?_
  apply Finset.sum_congr rfl
  intro split _
  congr 1
  funext i
  cases i <;> rfl

/-- The divisor equation and derived three-point relation lower the calibration
power. This equality holds over the original coefficient algebra, before division. -/
theorem calibration_pairing_recursion (K : RationalTailIntersection G T P)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (beta : B) (hb : beta ≠ 0) (m : ℕ) (divisor : Omega.graded.degree 1) (x y : V) :
    A.divisorPairing divisor beta *
        Omega.pairing.form x (U.calibrationCoefficient (m+2) beta y) =
      (∑ split : ↥(D.positiveTailSplittings beta),
        U.invariant 0 (Option (Fin 2)) split.val.1 0
          (Option.casesOn · (U.calibrationCoefficient (m+1) split.val.2 y) ![divisor.val,x])) -
        Omega.pairing.form x
          (U.calibrationCoefficient (m+1) beta (L.divisorAction divisor y)) := by
  have hd := H.global_divisor_of_ne_zero 0 (Fin 2) beta ![0,m+1] ![x,y] divisor hb
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add] at hd
  have hk : lowerPower (![0,m+1] : Fin 2 → ℕ) 1 = ![0,m] := by
    funext i
    fin_cases i
    · rfl
    · change m + 1 - 1 = m
      exact Nat.add_sub_cancel m 1
  have ha : replaceInput (![x,y] : Fin 2 → V) 1 (L.divisorAction divisor y) =
      ![x,L.divisorAction divisor y] := by
    funext i
    fin_cases i <;> rfl
  rw [hk, ha] at hd
  rw [U.calibrationCoefficient_pairing, U.calibrationCoefficient_pairing]
  apply (eq_sub_iff_add_eq).mpr
  refine hd.symm.trans ?_
  convert K.threePoint_divisor beta m divisor.val x y using 1
  congr 1 <;> funext i <;> cases i <;> rfl

end RationalTailIntersection
end AxiomaticGW
