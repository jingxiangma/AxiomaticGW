/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.PointTarget.DVVCalculation

/-! # Termination of point-target descendant reconstruction

Merging lowers the sum of the marked cotangent powers by one. The nonseparating
normalization lowers it by two, and each factor in a separating term has at most that
total. This bound is independent of the genus and the number of zero-power markings.
-/

@[expose] public section
namespace AxiomaticGW.PointTarget.DVVCalculation

/-- Canonical profiles preserve the total cotangent weight. -/
theorem profile_sum {S : Type} [Fintype S] (d : S → ℕ) :
    (profile d).sum = ∑ s, d s := by
  exact congrArg Multiset.sum (sortedPowers_multiset (Finset.univ.val.map d))

/-- A positive power, when present, comes first in the canonical profile. -/
theorem profile_pairwise {S : Type} [Fintype S] (d : S → ℕ) : (profile d).Pairwise (· ≥ ·) := by
  have h (m : Multiset ℕ) : (sortedPowers m).Pairwise (· ≥ ·) :=
    Quot.inductionOn m (fun l ↦ List.pairwise_insertionSort (· ≥ ·) l)
  exact h _

private theorem subweight {S : Type} [Fintype S] (T : Finset S) (d : S → ℕ) :
    (∑ t : T, d t) ≤ ∑ s, d s := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ T)

/-- Every occurrence of a vertex in the original three DVV contractions has strictly
smaller total cotangent weight than the request on the left. -/
theorem contractions_congr_weight {A : Type*} [AddCommMonoid A]
    (scale : ℚ → A → A) (product : A → A → A)
    (J K : (b : ℕ) → (S : Type) → [Fintype S] → (S → ℕ) → A)
    (g k : ℕ) {S : Type} [Fintype S] [DecidableEq S] (d : S → ℕ)
    (agree : ∀ (b : ℕ) (T : Type) [Fintype T] (e : T → ℕ),
      (∑ t, e t) < k + 1 + ∑ s, d s → J b T e = K b T e) :
    dvvContractions scale product J g k S d = dvvContractions scale product K g k S d := by
  unfold dvvContractions
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    apply congrArg (scale _)
    apply agree
    rw [Finset.sum_update_of_mem (Finset.mem_univ s) d, Finset.sdiff_singleton_eq_erase]
    have h := Finset.add_sum_erase Finset.univ d (Finset.mem_univ s)
    omega
  · apply congrArg (scale _)
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]
    rw [if_neg hk, if_neg hk]
    apply Finset.sum_congr rfl
    intro ab hab
    have hsum := Finset.mem_antidiagonal.mp hab
    apply congrArg (scale _)
    congr 1
    · by_cases hg : g = 0
      · rw [if_pos hg, if_pos hg]
      rw [if_neg hg, if_neg hg]
      apply agree
      simp only [Fintype.sum_option]
      omega
    · apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      · apply agree
        simp only [Fintype.sum_option]
        have h := subweight T d
        omega
      · apply agree
        simp only [Fintype.sum_option]
        have h := subweight (Finset.univ \ T) d
        omega

private theorem recursive_shape (g : ℕ) (p : List ℕ) (sorted : p.Pairwise (· ≥ ·))
    (stable : 3 ≤ 2 * g + p.length) (top : p.sum = 3 * g + p.length - 3)
    (hz : ¬ (g = 0 ∧ p = [0, 0, 0])) (ho : ¬ (g = 1 ∧ p = [1])) :
    ∃ k r, p = (k + 1) :: r ∧ 3 ≤ 2 * g + r.length := by
  have pos : 0 < p.sum := by
    by_contra! h
    have hs : p.sum = 0 := by omega
    have hg : g = 0 := by omega
    have hn : p.length = 3 := by omega
    exact hz ⟨hg, List.eq_replicate_iff.mpr ⟨hn, List.sum_eq_zero_iff_forall_eq_nat.mp hs⟩⟩
  cases p with
  | nil => simp only [List.sum_nil, lt_irrefl] at pos
  | cons a r =>
    simp only [List.length_cons, List.sum_cons] at stable top pos
    have ha : 0 < a := by
      by_contra! h
      have hr : r.sum = 0 := List.sum_eq_zero_iff_forall_eq_nat.mpr fun x hx ↦ by
        have ht := (List.pairwise_cons.mp sorted).1 x hx
        omega
      omega
    have ht : 3 ≤ 2 * g + r.length := by
      by_contra! h
      have hg : g = 1 := by omega
      have hr : r = [] := List.length_eq_zero_iff.mp (by omega)
      subst r
      simp only [List.sum_nil, List.length_nil] at top
      have ha1 : a = 1 := by omega
      exact ho ⟨hg, congrArg (fun x ↦ [x]) ha1⟩
    cases a with
    | zero => omega
    | succ k => exact ⟨k, r, rfl, ht⟩

/-- After more steps than the total cotangent weight, every leaf drops out of the evaluation.
The proof applies to any two assignments of rational numbers to unresolved integral keys. -/
theorem expand_independent (w w' : Key → ℚ) (depth g : ℕ) (p : List ℕ)
    (sorted : p.Pairwise (· ≥ ·)) (bound : p.sum < depth) :
    RationalTerms.eval w (expand depth g p) = RationalTerms.eval w' (expand depth g p) := by
  induction depth generalizing g p with
  | zero => omega
  | succ n ih =>
    change RationalTerms.eval w (expandStep (expand n) g p) =
      RationalTerms.eval w' (expandStep (expand n) g p)
    rw [expandStep.eq_def]
    by_cases hd : 2 * g + p.length < 3 ∨ p.sum ≠ 3 * g + p.length - 3
    · simp only [hd, ↓reduceIte, RationalTerms.eval_zero]
    rw [if_neg hd]
    by_cases hz : g = 0 ∧ p = [0, 0, 0]
    · rw [if_pos hz, RationalTerms.eval_term, RationalTerms.eval_term, Multiset.map_zero,
        Multiset.map_zero]
    rw [if_neg hz]
    by_cases ho : g = 1 ∧ p = [1]
    · rw [if_pos ho, RationalTerms.eval_term, RationalTerms.eval_term, Multiset.map_zero,
        Multiset.map_zero]
    rw [if_neg ho]
    push Not at hd
    obtain ⟨k, r, rfl, hr⟩ := recursive_shape g p sorted hd.1 hd.2 hz ho
    simp only [hr, ↓reduceIte, RationalTerms.eval_scale, eval_row]
    congr 1
    apply contractions_congr_weight
    intro b T _ e he
    apply ih b _ (profile_pairwise e)
    rw [profile_sum]
    have hsum : ∑ s, r.get s = r.sum := by rw [← List.sum_ofFn, List.ofFn_get]
    rw [hsum] at he
    simp only [List.sum_cons] at bound
    omega

/-- Total rational calculation for the point target, in any genus and any marking order. -/
def number (g : ℕ) (p : List ℕ) : ℚ :=
  RationalTerms.eval (fun _ : Key ↦ (0 : ℚ)) (expand (p.sum + 1) g (profile p.get))

/-- The total evaluator agrees with every geometric realization satisfying DVV and its
two initial values, including off-dimension and unstable requests. -/
theorem number_eq_value {C : StableCurveCohomology ℚ} (P : PsiClasses C)
    (I : StableCurveIntegration C) (dvv : DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24)
    (g : ℕ) (p : List ℕ) : number g p = value P I g p := by
  have hs : (profile p.get).sum = p.sum := by
    rw [profile_sum, ← List.sum_ofFn, List.ofFn_get]
  rw [number, expand_independent _ (fun t ↦ value P I t.1 t.2) _ _ _
    (profile_pairwise _) (by omega), expand_value P I dvv zero one, value_profile]
  rfl

/-- Original finite marking types use their sorted cotangent profile, including zeros. -/
theorem number_profile_eq_intersectionNumber {C : StableCurveCohomology ℚ} (P : PsiClasses C)
    (I : StableCurveIntegration C) (dvv : DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24)
    (g : ℕ) {S : Type} [Fintype S] (d : S → ℕ) :
    number g (profile d) = intersectionNumber P I g S d :=
  (number_eq_value P I dvv zero one g _).trans (value_profile P I g d)

/-- Two geometric systems with the same normalized point-target equations agree on every
ordered cotangent integral, across all genera and marking arities. -/
theorem intersectionNumber_unique {C C' : StableCurveCohomology ℚ} (P : PsiClasses C)
    (I : StableCurveIntegration C) (P' : PsiClasses C') (I' : StableCurveIntegration C')
    (dvv : DVVRecursion P I) (dvv' : DVVRecursion P' I')
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24)
    (zero' : value P' I' 0 [0, 0, 0] = 1) (one' : value P' I' 1 [1] = 1 / 24)
    (g : ℕ) {S : Type} [Fintype S] (d : S → ℕ) :
    intersectionNumber P I g S d = intersectionNumber P' I' g S d :=
  (number_profile_eq_intersectionNumber P I dvv zero one g d).symm.trans
    (number_profile_eq_intersectionNumber P' I' dvv' zero' one' g d)

end AxiomaticGW.PointTarget.DVVCalculation
