/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.CollectedTerms
public import AxiomaticGW.Combinatorics.MarkingPowers
public import AxiomaticGW.PointTarget.Descendants
public import Mathlib.Data.Multiset.Sort

/-! # Finite calculations with the point-target DVV relation

Each lookup retains the genus and the multiset of cotangent powers, including repeated
powers. The separating terms range over all subsets of the original labeled markings.
-/

@[expose] public section
namespace AxiomaticGW.PointTarget.DVVCalculation
variable {C : StableCurveCohomology ℚ}

/-- Sort the small multiset of vertex powers by structural insertion. This representative
reduces in the kernel when a closed numerical certificate compares complete term lists. -/
def sortedPowers (m : Multiset ℕ) : List ℕ :=
  Quot.liftOn m (List.insertionSort (· ≥ ·)) fun l r h ↦ by
    have hp := (List.perm_insertionSort (· ≥ ·) l).trans
      (h.trans (List.perm_insertionSort (· ≥ ·) r).symm)
    exact hp.eq_of_pairwise' (r := (· ≥ ·))
      (List.pairwise_insertionSort _ l) (List.pairwise_insertionSort _ r)

/-- Sorting retains all multiplicities. -/
theorem sortedPowers_multiset (m : Multiset ℕ) : (sortedPowers m : Multiset ℕ) = m :=
  Quot.inductionOn m fun l ↦ Quot.sound (List.perm_insertionSort (· ≥ ·) l)

/-- Cotangent powers in decreasing order. A repeated exponent occurs once per marking. -/
def profile {S : Type} [Fintype S] (d : S → ℕ) : List ℕ :=
  sortedPowers (Finset.univ.val.map d)

/-- The original point-target integral with the list positions as its marked points. -/
noncomputable def value (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (p : List ℕ) : ℚ := intersectionNumber P I g (Fin p.length) p.get

/-- A sorted list lookup gives the integral on the original labeling, also at unstable arity. -/
theorem value_of_powers (P : PsiClasses C) (I : StableCurveIntegration C)
    {S : Type} [Fintype S] (g : ℕ) (d : S → ℕ) {p : List ℕ}
    (hp : Finset.univ.val.map d = (p : Multiset ℕ)) :
    value P I g p = intersectionNumber P I g S d := by
  obtain ⟨e, he⟩ := markingEquiv_of_powers d p.get
    (hp.trans (by rw [Fin.univ_val_map, List.ofFn_get]))
  by_cases h : StableArity g S
  · have hd : (fun t ↦ d (e.symm t)) = p.get := by
      funext t
      simpa only [Equiv.apply_symm_apply] using (he (e.symm t)).symm
    rw [value, ← hd]
    exact intersectionNumber_relabel P I g _ _ h ((StableArity.equiv e).mp h) e d
  · rw [value, intersectionNumber_of_unstable _ _ _ _ (fun ht ↦ h ((StableArity.equiv e).mpr ht)),
      intersectionNumber_of_unstable _ _ _ _ h]

/-- Geometric meaning of every finite lookup appearing on the right side of DVV. -/
theorem value_profile (P : PsiClasses C) (I : StableCurveIntegration C)
    {S : Type} [Fintype S] (g : ℕ) (d : S → ℕ) :
    value P I g (profile d) = intersectionNumber P I g S d :=
  value_of_powers P I g d (sortedPowers_multiset _).symm

/-- A terminal variable retains its genus and every cotangent power. -/
abbrev Key := ℕ × List ℕ

/-- The original DVV contractions, with unresolved branches retained as polynomial terms. -/
def row (V : ℕ → List ℕ → RationalTerms Key) (g k : ℕ) (p : List ℕ) : RationalTerms Key :=
  dvvContractions RationalTerms.scale RationalTerms.mul (fun b _ _ e ↦ V b (profile e))
    g k (Fin p.length) p.get

/-- Evaluating a symbolic row commutes with both weighted sums and separating products. -/
theorem eval_row (V : ℕ → List ℕ → RationalTerms Key) (w : Key → ℚ) (g k : ℕ)
    (p : List ℕ) : RationalTerms.eval w (row V g k p) =
      dvvContractions (· * ·) (· * ·) (fun b _ _ e ↦ RationalTerms.eval w (V b (profile e)))
        g k (Fin p.length) p.get := by
  by_cases hk : k = 0 <;> by_cases hg : g = 0 <;>
    simp only [row, dvvContractions, hk, hg, ↓reduceIte, RationalTerms.eval_add,
      RationalTerms.eval_sum, RationalTerms.eval_scale, RationalTerms.eval_mul,
      RationalTerms.eval_zero, Algebra.algebraMap_self_apply]

/-- Evaluation of the actual polynomial row at sound branch expressions gives the
original DVV equation, with its leading odd double factorial. -/
theorem row_value (P : PsiClasses C) (I : StableCurveIntegration C) (D : DVVRecursion P I)
    (V : ℕ → List ℕ → RationalTerms Key) (w : Key → ℚ)
    (hv : ∀ b p, RationalTerms.eval w (V b p) = value P I b p)
    (g k : ℕ) (p : List ℕ) (h : StableArity g (Fin p.length)) :
    (oddDoubleFactorial (k + 1) : ℚ) * value P I g ((k + 1) :: p) =
      RationalTerms.eval w (row V g k p) := by
  let d : Option (Fin p.length) → ℕ := fun | none => k + 1 | some s => p.get s
  have hp : Finset.univ.val.map d = (((k + 1) :: p : List ℕ) : Multiset ℕ) := by
    change ((none ::ₘ Finset.univ.val.map some).map d) = _
    rw [Multiset.map_cons, Multiset.map_map]
    change (k + 1) ::ₘ Finset.univ.val.map p.get = _
    rw [Fin.univ_val_map, List.ofFn_get]
    rfl
  rw [value_of_powers P I g d hp]
  have lookup : (fun (b : ℕ) (S : Type) [Fintype S] (e : S → ℕ) ↦
      RationalTerms.eval w (V b (profile e))) = intersectionNumber P I := by
    funext b S _ e
    rw [hv, value_profile]
  rw [eval_row, lookup]
  have hd := D g k (Fin p.length) h p.get
  simp only [Algebra.algebraMap_self_apply] at hd
  refine Eq.trans ?_ hd
  apply congrArg ((oddDoubleFactorial (k + 1) : ℚ) * ·)
  apply congrArg (intersectionNumber P I g (Option (Fin p.length)))
  funext x
  cases x <;> rfl

/-- Apply one DVV equation, carrying symbolic boundary values for unavailable rows. -/
def expandStep (V : ℕ → List ℕ → RationalTerms Key) (g : ℕ) (p : List ℕ) :
    RationalTerms Key :=
    if 2 * g + p.length < 3 ∨ p.sum ≠ 3 * g + p.length - 3 then 0
    else if g = 0 ∧ p = [0, 0, 0] then RationalTerms.term 1 0
    else if g = 1 ∧ p = [1] then RationalTerms.term (1 / 24) 0
    else match p with
      | [] => RationalTerms.term 1 {(g, [])}
      | 0 :: r => RationalTerms.term 1 {(g, 0 :: r)}
      | (k + 1) :: r => if 3 ≤ 2 * g + r.length then
          RationalTerms.scale (oddDoubleFactorial (k + 1) : ℚ)⁻¹ (row V g k r)
        else RationalTerms.term 1 {(g, (k + 1) :: r)}

/-- Bounded expansion in the original DVV equations. Unresolved variables persist
symbolically, and zero or unstable factors kill their whole separating term. -/
def expand (depth : ℕ) : ℕ → List ℕ → RationalTerms Key :=
  Nat.rec (motive := fun _ ↦ ℕ → List ℕ → RationalTerms Key)
    (fun g p ↦ RationalTerms.term 1 {(g, p)}) (fun _ ↦ expandStep) depth

private theorem off_degree (P : PsiClasses C) (I : StableCurveIntegration C) (g : ℕ) (p : List ℕ)
    (h : 2 * g + p.length < 3 ∨ p.sum ≠ 3 * g + p.length - 3) : value P I g p = 0 := by
  unfold value
  by_cases hs : StableArity g (Fin p.length)
  · apply intersectionNumber_eq_zero_of_degree_ne _ _ _ _ hs
    have hsum : ∑ i, p.get i = p.sum := by rw [← List.sum_ofFn, List.ofFn_get]
    rw [hsum, StableArity.dimension, Fintype.card_fin]
    simp only [StableArity, Fintype.card_fin] at hs
    exact h.resolve_left (Nat.not_lt.mpr hs)
  · exact intersectionNumber_of_unstable _ _ _ _ hs _

/-- The three-point volume on any fixed three labels supplies the rational DVV seed. -/
theorem initial_zero (P : PsiClasses C) (I : StableCurveIntegration C)
    {S : Type} [Fintype S] (hS : Fintype.card S = 3) (h : StableArity 0 S)
    (vol : I.integrate 0 S h 1 = 1) : value P I 0 [0, 0, 0] = 1 := by
  rw [value_of_powers P I 0 (S := S) (fun _ ↦ 0) (by
    rw [Multiset.map_const', ← Finset.card, Finset.card_univ, hS]; rfl),
    intersectionNumber_of_stable P I 0 S h, PsiClasses.monomial_zero, vol]

/-- The elliptic one-point seed in the usual cotangent-class normalization. -/
theorem initial_one (P : PsiClasses C) (I : StableCurveIntegration C)
    (vol : I.integrate 1 (Fin 1) genusOne_one_stable (P.psi 1 _ genusOne_one_stable 0) =
      (1 / 24 : ℚ)) : value P I 1 [1] = 1 / 24 := by
  rw [value_of_powers P I 1 (S := Fin 1) (fun _ ↦ 1) (by decide +kernel)]
  exact intersectionNumber_one_one P I (by simpa only [Algebra.algebraMap_self_apply] using vol)

private theorem eval_variable (w : Key → ℚ) (a : Key) :
    RationalTerms.eval w (RationalTerms.term 1 {a}) = w a := by
  rw [RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul]

/-- Every partial expansion represents the original geometric integral, including
any unresolved leaves. A constant final polynomial gives a closed numerical certificate. -/
theorem expand_value (P : PsiClasses C) (I : StableCurveIntegration C) (D : DVVRecursion P I)
    (zero : value P I 0 [0, 0, 0] = 1) (one : value P I 1 [1] = 1 / 24) (depth g : ℕ)
    (p : List ℕ) :
    RationalTerms.eval (fun t : Key ↦ value P I t.1 t.2) (expand depth g p) = value P I g p := by
  induction depth generalizing g p with
  | zero => exact eval_variable _ _
  | succ n ih =>
    change RationalTerms.eval (fun t : Key ↦ value P I t.1 t.2) (expandStep (expand n) g p) = _
    rw [expandStep.eq_def]
    by_cases hd : 2 * g + p.length < 3 ∨ p.sum ≠ 3 * g + p.length - 3
    · rw [if_pos hd, RationalTerms.eval_zero, off_degree P I g p hd]
    rw [if_neg hd]
    by_cases hz : g = 0 ∧ p = [0, 0, 0]
    · rw [if_pos hz, hz.1, hz.2, zero, RationalTerms.eval_term, Multiset.map_zero,
        Multiset.prod_zero, map_one, mul_one]
    rw [if_neg hz]
    by_cases ho : g = 1 ∧ p = [1]
    · rw [if_pos ho, ho.1, ho.2, one, RationalTerms.eval_term, Multiset.map_zero,
        Multiset.prod_zero, Algebra.algebraMap_self_apply, mul_one]
    rw [if_neg ho]
    cases p with
    | nil => exact eval_variable _ _
    | cons d r =>
      cases d with
      | zero => exact eval_variable _ _
      | succ k =>
        dsimp only
        by_cases hs : 3 ≤ 2 * g + r.length
        · have hst : StableArity g (Fin r.length) := by
            simpa only [StableArity, Fintype.card_fin] using hs
          have hn : (oddDoubleFactorial (k + 1) : ℚ) ≠ 0 := by
            unfold oddDoubleFactorial
            exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun i _ ↦ by omega)
          simp only [hs, ↓reduceIte, RationalTerms.eval_scale, Algebra.algebraMap_self_apply,
            ← row_value P I D _ _ ih g k r hst, inv_mul_cancel_left₀ hn]
        · simpa only [hs, ↓reduceIte] using
            eval_variable (fun t : Key ↦ value P I t.1 t.2) (g, (k + 1) :: r)

end AxiomaticGW.PointTarget.DVVCalculation
