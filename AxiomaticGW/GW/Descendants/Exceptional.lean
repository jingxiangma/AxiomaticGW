/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GW.Descendants.Equations

/-!
# Exceptional terms in numerical descendant equations

The signed dilaton coefficient is meaningful at every curve arity. The string
equation has a degree-zero genus-zero three-point metric term, and the dilaton
equation has a degree-zero genus-one one-point term supplied by the target.
These terms are separate from auxiliary degree-zero unstable invariant values.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

/-- The signed coefficient `2g - 2 + |S|` in the dilaton equation. -/
def dilatonCoefficient (R : Type*) [CommRing R] (g : ℕ)
    (S : Type*) [Fintype S] : R :=
  ((2 * g + Fintype.card S : ℕ) : R) - 2

/-- On stable curve arities the signed coefficient agrees with the existing
natural-number expression. -/
theorem dilatonCoefficient_eq_natCast (R : Type*) [CommRing R]
    (g : ℕ) (S : Type*) [Fintype S] (h : StableArity g S) :
    dilatonCoefficient R g S = ((2 * g + Fintype.card S - 2 : ℕ) : R) := by
  have hle : 2 ≤ 2 * g + Fintype.card S := by
    unfold StableArity at h
    omega
  rw [Nat.cast_sub hle]
  simp only [dilatonCoefficient, Nat.cast_ofNat]

theorem dilatonCoefficient_zero_empty (R : Type*) [CommRing R] :
    dilatonCoefficient R 0 Empty = -2 := by
  simp only [dilatonCoefficient, Nat.mul_zero, Fintype.card_eq_zero, zero_add,
    Nat.cast_zero, zero_sub]

theorem dilatonCoefficient_zero_fin_one (R : Type*) [CommRing R] :
    dilatonCoefficient R 0 (Fin 1) = -1 := by
  simp only [dilatonCoefficient, Nat.mul_zero, Fintype.card_fin, zero_add,
    Nat.cast_one]
  ring

theorem dilatonCoefficient_one_empty (R : Type*) [CommRing R] :
    dilatonCoefficient R 1 Empty = 0 := by
  simp only [dilatonCoefficient, mul_one, Fintype.card_eq_zero, Nat.add_zero,
    Nat.cast_ofNat, sub_self]

theorem dilatonCoefficient_relabel (R : Type*) [CommRing R]
    (g : ℕ) (S T : Type*) [Fintype S] [Fintype T] (e : S ≃ T) :
    dilatonCoefficient R g T = dilatonCoefficient R g S := by
  simp only [dilatonCoefficient, Fintype.card_congr e]

/-- The metric evaluated on two labelled inputs, and zero at every other
arity. Averaging the two orders makes the definition independent of a chosen
enumeration of the labels. -/
noncomputable def twoPointPairing {R V : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] (P : SymmetricPerfectPairing R V)
    (S : Type*) [Fintype S] (a : S → V) : R := by
  classical
  exact if Fintype.card S = 2 then
    algebraMap ℚ R (1 / 2 : ℚ) *
      ∑ s, ∑ t, if s = t then 0 else P.form (a s) (a t)
  else 0

theorem twoPointPairing_eq_zero_of_card_ne_two
    {R V : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] (P : SymmetricPerfectPairing R V)
    (S : Type*) [Fintype S] (a : S → V) (h : Fintype.card S ≠ 2) :
    twoPointPairing P S a = 0 := by
  simp only [twoPointPairing, h, ↓reduceIte]

theorem twoPointPairing_fin_two
    {R V : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] (P : SymmetricPerfectPairing R V)
    (a : Fin 2 → V) :
    twoPointPairing P (Fin 2) a = P.form (a 0) (a 1) := by
  simp only [twoPointPairing, Fintype.card_fin, ↓reduceIte, Fin.sum_univ_two,
    Fin.isValue, zero_ne_one, one_ne_zero,
    zero_add, add_zero, P.isSymm.eq (a 1) (a 0)]
  have hhalf : algebraMap ℚ R (1 / 2 : ℚ) * 2 = 1 := by
    have hrat : (1 / 2 : ℚ) * 2 = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap ℚ R) hrat
  calc
    algebraMap ℚ R (1 / 2 : ℚ) *
        (P.form (a 0) (a 1) + P.form (a 0) (a 1)) =
        (algebraMap ℚ R (1 / 2 : ℚ) * 2) * P.form (a 0) (a 1) := by ring
    _ = P.form (a 0) (a 1) := by rw [hhalf, one_mul]

/-- The two-input metric is natural under arbitrary relabelling. -/
theorem twoPointPairing_relabel
    {R V : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] (P : SymmetricPerfectPairing R V)
    (S T : Type*) [Fintype S] [Fintype T] (e : S ≃ T) (a : S → V) :
    twoPointPairing P T (fun t ↦ a (e.symm t)) = twoPointPairing P S a := by
  classical
  unfold twoPointPairing
  rw [← Fintype.card_congr e]
  split_ifs
  · congr 1
    apply Fintype.sum_equiv e.symm
    intro s
    apply Fintype.sum_equiv e.symm
    intro t
    simp only [e.symm.injective.eq_iff]
  · rfl

/-- Exceptional metric term for insertion of the primary unit. It is supported
at genus zero, degree zero, two remaining labels, and zero cotangent powers. -/
noncomputable def stringCorrection {R V B : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Zero B]
    (P : SymmetricPerfectPairing R V) (g : ℕ) (S : Type*) [Fintype S]
    (beta : B) (k : S → ℕ) (a : S → V) : R := by
  classical
  exact if g = 0 ∧ beta = 0 ∧ (∀ s, k s = 0) then twoPointPairing P S a else 0

theorem stringCorrection_eq_zero_of_stable
    {R V B : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Zero B]
    (P : SymmetricPerfectPairing R V) (g : ℕ) (S : Type*) [Fintype S]
    (beta : B) (k : S → ℕ) (a : S → V) (h : StableArity g S) :
    stringCorrection P g S beta k a = 0 := by
  classical
  unfold stringCorrection
  split_ifs with hex
  · have hn : Fintype.card S ≠ 2 := by
      unfold StableArity at h
      rcases hex with ⟨rfl, _, _⟩
      omega
    exact twoPointPairing_eq_zero_of_card_ne_two P S a hn
  · rfl

theorem stringCorrection_eq_zero_of_ne_zero
    {R V B : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Zero B]
    (P : SymmetricPerfectPairing R V) (g : ℕ) (S : Type*) [Fintype S]
    (beta : B) (k : S → ℕ) (a : S → V) (h : beta ≠ 0) :
    stringCorrection P g S beta k a = 0 := by
  simp only [stringCorrection, h, false_and, and_false, ↓reduceIte]

theorem stringCorrection_eq_zero_of_card_ne_two
    {R V B : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Zero B]
    (P : SymmetricPerfectPairing R V) (g : ℕ) (S : Type*) [Fintype S]
    (beta : B) (k : S → ℕ) (a : S → V) (h : Fintype.card S ≠ 2) :
    stringCorrection P g S beta k a = 0 := by
  simp only [stringCorrection, twoPointPairing_eq_zero_of_card_ne_two P S a h,
    ite_self]

theorem stringCorrection_relabel
    {R V B : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Zero B]
    (P : SymmetricPerfectPairing R V) (g : ℕ) (S T : Type*)
    [Fintype S] [Fintype T] (e : S ≃ T) (beta : B) (k : S → ℕ) (a : S → V) :
    stringCorrection P g T beta (fun t ↦ k (e.symm t)) (fun t ↦ a (e.symm t)) =
      stringCorrection P g S beta k a := by
  have hk : (∀ t, k (e.symm t) = 0) ↔ ∀ s, k s = 0 := by
    constructor
    · intro h s
      simpa only [e.symm_apply_apply] using h (e s)
    · intro h t
      exact h (e.symm t)
  classical
  by_cases h : g = 0 ∧ beta = 0 ∧ ∀ s, k s = 0
  · simp only [stringCorrection, h, and_self, implies_true, ↓reduceIte,
      twoPointPairing_relabel P S T e a]
  · have ht : ¬(g = 0 ∧ beta = 0 ∧ ∀ t, k (e.symm t) = 0) := by
      intro ht
      exact h ⟨ht.1, ht.2.1, hk.mp ht.2.2⟩
    simp only [stringCorrection, h, ht, ↓reduceIte]

theorem stringCorrection_zero_fin_two
    {R V B : Type*} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Zero B]
    (P : SymmetricPerfectPairing R V) (a : Fin 2 → V) :
    stringCorrection P 0 (Fin 2) (0 : B) (fun _ ↦ 0) a =
      P.form (a 0) (a 1) := by
  simp only [stringCorrection, and_self, implies_true, ↓reduceIte,
    twoPointPairing_fin_two]

/-- The genus-one degree-zero dilaton correction. Its value is target data;
the point target supplies `1/24`, rather than a universal value for all targets. -/
noncomputable def dilatonCorrection {R B : Type*} [CommRing R] [Zero B]
    (c : R) (g : ℕ) (S : Type*) [Fintype S] (beta : B) : R := by
  classical
  exact if g = 1 ∧ beta = 0 ∧ Fintype.card S = 0 then c else 0

theorem dilatonCorrection_eq_zero_of_stable
    {R B : Type*} [CommRing R] [Zero B]
    (c : R) (g : ℕ) (S : Type*) [Fintype S] (beta : B)
    (h : StableArity g S) : dilatonCorrection c g S beta = 0 := by
  classical
  unfold dilatonCorrection
  split_ifs with hex
  · unfold StableArity at h
    rcases hex with ⟨rfl, _, hc⟩
    omega
  · rfl

theorem dilatonCorrection_eq_zero_of_ne_zero
    {R B : Type*} [CommRing R] [Zero B]
    (c : R) (g : ℕ) (S : Type*) [Fintype S] (beta : B) (h : beta ≠ 0) :
    dilatonCorrection c g S beta = 0 := by
  simp only [dilatonCorrection, h, false_and, and_false, ↓reduceIte]

theorem dilatonCorrection_eq_zero_of_card_ne_zero
    {R B : Type*} [CommRing R] [Zero B]
    (c : R) (g : ℕ) (S : Type*) [Fintype S] (beta : B)
    (h : Fintype.card S ≠ 0) : dilatonCorrection c g S beta = 0 := by
  simp only [dilatonCorrection, h, and_false, ↓reduceIte]

theorem dilatonCorrection_relabel
    {R B : Type*} [CommRing R] [Zero B]
    (c : R) (g : ℕ) (S T : Type*) [Fintype S] [Fintype T]
    (e : S ≃ T) (beta : B) :
    dilatonCorrection c g T beta = dilatonCorrection c g S beta := by
  unfold dilatonCorrection
  rw [Fintype.card_congr e]

theorem dilatonCorrection_one_empty
    {R B : Type*} [CommRing R] [Zero B] (c : R) :
    dilatonCorrection c 1 Empty (0 : B) = c := by
  simp only [dilatonCorrection, Fintype.card_eq_zero, and_self, ↓reduceIte]

end AxiomaticGW
