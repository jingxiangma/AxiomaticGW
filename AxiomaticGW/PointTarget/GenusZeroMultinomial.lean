/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.LowGenus
public import AxiomaticGW.Tautological.ForgetfulIntegrals
public import AxiomaticGW.PointTarget.DVVCalculation

/-! # The point-target genus-zero multinomial from the universal curve

A top-degree cotangent monomial on a stable rational curve always has a zero marking.
The geometric string equation deletes it and lowers a positive exponent. The labeled
factorial ratio satisfies precisely that sum, starting at the three-point volume.
-/

@[expose] public section
namespace AxiomaticGW.PointTarget
open PsiBoundaryExpansion

private def multinomial {S : Type} [Fintype S] (d : S → ℕ) : ℚ :=
  ((∑ s, d s).factorial : ℚ) / ∏ s, ((d s).factorial : ℚ)

private theorem sum_lower {S : Type} [Fintype S] [DecidableEq S] (d : S → ℕ)
    (i : S) (hi : d i ≠ 0) : (∑ s, Function.update d i (d i - 1) s) = (∑ s, d s) - 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i) d, Finset.sdiff_singleton_eq_erase]
  have h := Finset.add_sum_erase Finset.univ d (Finset.mem_univ i)
  omega

private theorem factorial_lower {S : Type} [Fintype S] [DecidableEq S] (d : S → ℕ)
    (i : S) (hi : d i ≠ 0) :
    (d i : ℚ) * (∏ s, ((Function.update d i (d i - 1) s).factorial : ℚ)) =
      ∏ s, ((d s).factorial : ℚ) := by
  let f := fun s ↦ ((d s).factorial : ℚ)
  have upd : (fun s ↦ ((Function.update d i (d i - 1) s).factorial : ℚ)) =
      Function.update f i (((d i - 1).factorial : ℕ) : ℚ) := by
    funext s
    by_cases hs : s = i
    · subst s
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hs, f]
  rw [upd, Finset.prod_update_of_mem (Finset.mem_univ i) f, Finset.sdiff_singleton_eq_erase,
    ← mul_assoc]
  have hf : (d i : ℚ) * ((d i - 1).factorial : ℚ) = f i := by
    have e : d i - 1 + 1 = d i := by omega
    have h := Nat.factorial_succ (d i - 1)
    rw [e] at h
    dsimp only [f]
    exact_mod_cast h.symm
  rw [hf]
  exact Finset.mul_prod_erase _ _ (Finset.mem_univ i)

/-- The factorial ratio obeys the labeled string recurrence at every positive total weight. -/
private theorem multinomial_string {S : Type} [Fintype S] [DecidableEq S] (d : S → ℕ)
    (hd : 0 < ∑ s, d s) :
    (∑ s, if d s = 0 then 0 else multinomial (Function.update d s (d s - 1))) =
      multinomial d := by
  let c : ℚ := (((∑ s, d s) - 1).factorial : ℚ) / ∏ s, ((d s).factorial : ℚ)
  have term (s : S) : (if d s = 0 then 0 else multinomial (Function.update d s (d s - 1))) =
      (d s : ℚ) * c := by
    by_cases hs : d s = 0
    · simp only [hs, ↓reduceIte, Nat.cast_zero, zero_mul]
    rw [if_neg hs, multinomial, sum_lower d s hs]
    dsimp only [c]
    rw [← factorial_lower d s hs]
    field_simp [show (d s : ℚ) ≠ 0 by exact_mod_cast hs]
  simp only [term, ← Finset.sum_mul, ← Nat.cast_sum]
  have e : (∑ s, d s) - 1 + 1 = ∑ s, d s := by omega
  have h := Nat.factorial_succ ((∑ s, d s) - 1)
  rw [e] at h
  rw [multinomial, h, Nat.cast_mul, mul_div_assoc]


variable {C : StableCurveCohomology ℚ} {I : StableCurveIntegration C}
    (U : ForgetfulPushforward C I) (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (T : TailForgetCompatible C)
    (vol : I.integrate 0 (Option Bool) tailStable 1 = 1)

include U F N K hK T vol

private theorem multinomial_geometry (n : ℕ) :
    ∀ (S : Type) [Fintype S], Fintype.card S = n →
      ∀ (_h : StableArity 0 S) (d : S → ℕ), (∑ s, d s) = n - 3 →
        intersectionNumber P I 0 S d = multinomial d := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S _ hn h d ht
    have stable : 3 ≤ n := by simpa only [StableArity, Nat.mul_zero, zero_add, hn] using h
    by_cases hthree : n = 3
    · have hsum : ∑ s, d s = 0 := by omega
      have hd : d = fun _ ↦ 0 :=
        funext (fun s ↦ Finset.sum_eq_zero_iff.mp hsum s (Finset.mem_univ s))
      subst d
      have src := DVVCalculation.initial_zero P I (by decide : Fintype.card (Option Bool) = 3)
        tailStable vol
      have hb := DVVCalculation.value_of_powers P I 0 (fun _ : S ↦ 0) (p := [0,0,0]) (by
        rw [Multiset.map_const', ← Finset.card, Finset.card_univ, hn, hthree]; rfl)
      rw [← hb, src]
      simp only [multinomial, Finset.sum_const_zero, Nat.factorial_zero, Nat.cast_one,
        Finset.prod_const_one, div_one]
    obtain ⟨z, hz⟩ : ∃ s, d s = 0 := by
      by_contra! hall
      have ble := Finset.sum_le_sum (s := (Finset.univ : Finset S)) (f := fun _ ↦ 1)
        (g := d) (fun s _ ↦ Nat.succ_le_of_lt (Nat.pos_of_ne_zero (hall s)))
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn] at ble
      omega
    let S' := {s : S // s ≠ z}
    let e : Option S' ≃ S := Equiv.optionSubtypeNe z
    let k : S' → ℕ := fun s ↦ d s
    have hn' : Fintype.card S' + 1 = n := by
      simpa only [Fintype.card_option, hn] using Fintype.card_congr e
    have hs' : StableArity 0 S' := by
      simp only [StableArity, Nat.mul_zero, zero_add]
      omega
    have he : (fun t : Option S' ↦ d (e t)) = (fun t ↦ t.elim 0 k) := by
      funext t
      cases t with
      | none => exact hz
      | some s => rfl
    have hsum : ∑ i, k i = ∑ i, d i := by
      rw [← e.sum_comp d, Fintype.sum_option]
      change _ = d z + ∑ i, k i
      rw [hz, zero_add]
    have hprod : (∏ i, ((k i).factorial : ℚ)) = ∏ i, ((d i).factorial : ℚ) := by
      rw [← e.prod_comp (fun s ↦ ((d s).factorial : ℚ)), Fintype.prod_option]
      change _ = ((d z).factorial : ℚ) * ∏ i, ((k i).factorial : ℚ)
      rw [hz, Nat.factorial_zero, Nat.cast_one, one_mul]
    calc
      _ = ∑ s : S', if k s = 0 then 0 else
          intersectionNumber P I 0 S' (Function.update k s (k s - 1)) := by
        rw [← intersectionNumber_relabel P I 0 S (Option S') h hs'.option e.symm d]
        simp only [Equiv.symm_symm, he, intersectionNumber_of_stable P I 0 _ hs'.option,
          intersectionNumber_of_stable P I 0 _ hs']
        simpa only [map_one, one_mul] using string_integral U F N P K hK T vol hs' 1 k
      _ = ∑ s, if k s = 0 then 0 else multinomial (Function.update k s (k s - 1)) := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases h0 : k s = 0
        · rw [if_pos h0, if_pos h0]
        rw [if_neg h0, if_neg h0]
        apply ih (Fintype.card S') (by omega) S' rfl hs'
        rw [sum_lower k s h0, hsum, ht]
        omega
      _ = multinomial k := multinomial_string k (by omega)
      _ = _ := by rw [multinomial, multinomial, hsum, hprod]

/-- All stable finite labeling sets have the top-dimensional factorial ratio and exact
off-dimension vanishing. -/
theorem genusZero_intersection_of_geometry {S : Type} [Fintype S]
    (h : StableArity 0 S) (d : S → ℕ) :
    intersectionNumber P I 0 S d = if (∑ s, d s) = Fintype.card S - 3 then
      ((Fintype.card S - 3).factorial : ℚ) / ∏ s, ((d s).factorial : ℚ) else 0 := by
  by_cases ht : (∑ s, d s) = Fintype.card S - 3
  · rw [if_pos ht, multinomial_geometry U F N P K hK T vol _ S rfl h d ht, multinomial, ht]
  · rw [if_neg ht]
    apply intersectionNumber_eq_zero_of_degree_ne P I _ _ h
    simpa only [StableArity.dimension, Nat.mul_zero, zero_add] using ht

/-- The rational string equation and the three-point volume realize the existing genus-zero
multinomial interface, including the vanishing away from the top degree. -/
theorem genusZeroPsiFormula_of_geometry : GenusZeroPsiFormula P I where
  formula n h d := by
    have hn : 3 ≤ n := by
      simpa only [StableArity, Nat.mul_zero, zero_add, Fintype.card_fin] using h
    rw [genusZero_intersection_of_geometry U F N P K hK T vol h d, Fintype.card_fin,
      genusZeroPsiValue, Algebra.algebraMap_self_apply]
    simp only [hn, true_and, Nat.cast_prod]

end AxiomaticGW.PointTarget
