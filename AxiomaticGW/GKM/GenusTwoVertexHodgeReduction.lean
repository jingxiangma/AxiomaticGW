/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-! # Reduced genus-two Hodge integrals at a surface localization vertex

Two tangent directions contribute λᵢλⱼ, with `0 ≤ i ≤ j ≤ 2` and `λ₀ = 1`.
The top-degree condition is `sum(powers) + i + j = 3 + n`. Removing string and
dilaton markings leaves a finite list of eight ordered seed keys.
-/

public section
namespace AxiomaticGW.GKM.GenusTwoVertexHodgeReduction

/-- The reduced keys `(i,j,sorted psi powers)` in the two-lambda genus-two sector. -/
@[expose] def seeds : Finset (ℕ × ℕ × List ℕ) :=
  {(0, 0, [4]), (0, 0, [2, 3]), (0, 0, [2, 2, 2]), (0, 1, [3]),
   (0, 1, [2, 2]), (0, 2, [2]), (1, 1, [2]), (1, 2, [])}

/-- The eight keys are distinct, including the unmarked integral of λ₁λ₂. -/
theorem card_seeds : seeds.card = 8 := by decide +kernel

private theorem twice_length_le (p : List ℕ) (h : ∀ k ∈ p, 2 ≤ k) : 2 * p.length ≤ p.sum := by
  induction p with
  | nil => decide
  | cons a p ih =>
    obtain ⟨ha, hp⟩ := List.forall_mem_cons.mp h
    have := ih hp
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Exact reduced support. The inequality `2n ≤ sum(powers)` bounds the length by three. -/
theorem mem_seeds_iff (i j : ℕ) (p : List ℕ) : (i, j, p) ∈ seeds ↔
    i ≤ j ∧ j ≤ 2 ∧ p.Pairwise (· ≤ ·) ∧ (∀ k ∈ p, 2 ≤ k) ∧ p.sum + i + j = 3 + p.length := by
  constructor
  · intro h
    simp only [seeds, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with h | h | h | h | h | h | h | h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> decide +kernel
  · rintro ⟨hij, hj, hs, hp, hd⟩
    have hn : p.length ≤ 3 := by have := twice_length_le p hp; omega
    rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩ <;>
      simp [seeds, List.pairwise_cons] at * <;> omega

/-- Order the two entries of a reduced pair. Every other admissible terminal shape
already has equal entries or at most one entry, by the dimension bound. -/
@[expose] def terminalPowers : List ℕ → List ℕ
  | [a, b] => if a ≤ b then [a, b] else [b, a]
  | p => p

/-- Canonicalization only permutes the original markings. -/
theorem terminalPowers_perm (p : List ℕ) : (terminalPowers p).Perm p := by
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩ <;> try exact .refl _
  change (if a ≤ b then [a, b] else [b, a]).Perm [a, b]
  split
  · exact .refl _
  · exact .swap _ _ _

/-- Normalizing an on-dimension list without a zero or a one yields its sorted seed key. -/
theorem reduced_key (i j : Fin 3) (hij : i ≤ j) (p : List ℕ)
    (hd : p.sum + (i : ℕ) + (j : ℕ) = 3 + p.length) (hz : 0 ∉ p) (ho : 1 ∉ p) :
    ((i : ℕ), (j : ℕ), terminalPowers p) ∈ seeds := by
  have perm := terminalPowers_perm p
  have large (k) (h : k ∈ p) : 2 ≤ k := by
    rcases k with _ | _ | k
    · exact (hz h).elim
    · exact (ho h).elim
    · omega
  refine (mem_seeds_iff ..).mpr ⟨hij, by omega, ?_, fun k hk ↦ large k (perm.mem_iff.mp hk), ?_⟩
  · have hn : p.length ≤ 3 := by have := twice_length_le p large; omega
    rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
    · exact .nil
    · exact List.pairwise_singleton ..
    · change (if a ≤ b then [a, b] else [b, a]).Pairwise (· ≤ ·)
      split <;> simp [List.pairwise_cons] <;> omega
    · simp [terminalPowers, List.pairwise_cons] at large hd ⊢
      omega
    · simp only [List.length_cons] at hn
      omega
  · rwa [perm.sum_eq, perm.length_eq]

private theorem shorter {p : List ℕ} {a : ℕ} (h : a ∈ p) : (p.erase a).length < p.length := by
  rw [List.length_erase_of_mem h]
  have := List.length_pos_of_mem h
  omega

/-- Lower one selected marking, retaining its position. String only uses positive entries. -/
@[expose] def lower (p : List ℕ) (k : Fin p.length) : List ℕ := p.set k.val (p.get k - 1)

/-- Numerical laws needed of a two-lambda vertex integral. The λ classes are pulled back
under forgetting a marking; their indices remain fixed in the two forgetful recurrences. -/
structure Recurrences (i j : ℕ) (V : List ℕ → ℚ) : Prop where
  /-- Only top complex degree integrates. -/
  degree : ∀ p, p.sum + i + j ≠ 3 + p.length → V p = 0
  /-- Relabeling marked points preserves the value. -/
  relabel : ∀ {p q}, p.Perm q → V p = V q
  /-- Each positive marked power can be lowered, with one summand for each occurrence. -/
  string : ∀ p, V (0 :: p) = ∑ k : Fin p.length, if 0 < p.get k then V (lower p k) else 0
  /-- The genus-two dilaton multiplier after erasing the extra marking is `2 + n`. -/
  dilaton : ∀ p, V (1 :: p) = ((2 + p.length : ℕ) : ℚ) * V p

/-- Evaluate with precisely the eight seed parameters using decreasing arity in both recurrences. -/
@[expose] def evaluate (seed : ↥seeds → ℚ) (i j : Fin 3) (hij : i ≤ j) (p : List ℕ) : ℚ :=
  if hd : p.sum + (i : ℕ) + (j : ℕ) = 3 + p.length then
    if hz : 0 ∈ p then
      let q := p.erase 0
      ∑ k : Fin q.length, if 0 < q.get k then evaluate seed i j hij (lower q k) else 0
    else if ho : 1 ∈ p then
      let q := p.erase 1
      ((2 + q.length : ℕ) : ℚ) * evaluate seed i j hij q
    else seed ⟨_, reduced_key i j hij p hd hz ho⟩
  else 0
termination_by p.length
decreasing_by
  · simpa only [lower, List.length_set] using shorter hz
  · exact shorter ho

/-- Terminal evaluation exposes the canonical sorted seed even if the input was unsorted. -/
theorem evaluate_reduced (seed : ↥seeds → ℚ) (i j : Fin 3) (hij : i ≤ j) (p : List ℕ)
    (hd : p.sum + (i : ℕ) + (j : ℕ) = 3 + p.length) (hz : 0 ∉ p) (ho : 1 ∉ p) :
    evaluate seed i j hij p = seed ⟨_, reduced_key i j hij p hd hz ho⟩ := by
  rw [evaluate, dif_pos hd, dif_neg hz, dif_neg ho]

/-- Any values satisfying the explicit dimension, symmetry, string, and dilaton laws are
recovered from their eight seed values. No geometric or numerical seed values are postulated. -/
theorem evaluate_sound (seed : ↥seeds → ℚ) (i j : Fin 3) (hij : i ≤ j)
    (V : List ℕ → ℚ) (laws : Recurrences i j V)
    (hseed : ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ seeds), seed ⟨_, hk⟩ = V p)
    (p : List ℕ) : evaluate seed i j hij p = V p := by
  rw [evaluate]
  split_ifs with hd hz ho
  · rw [laws.relabel (List.perm_cons_erase hz), laws.string]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · exact evaluate_sound seed i j hij V laws hseed _
    · rfl
  · rw [laws.relabel (List.perm_cons_erase ho), laws.dilaton]
    exact congrArg (_ * ·) (evaluate_sound seed i j hij V laws hseed _)
  · exact (hseed _ _).trans (laws.relabel (terminalPowers_perm p))
  · exact (laws.degree p hd).symm
termination_by p.length
decreasing_by
  · simpa only [lower, List.length_set] using shorter hz
  · exact shorter ho

end AxiomaticGW.GKM.GenusTwoVertexHodgeReduction
