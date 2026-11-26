/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.GenusTwoVertexHodgeReduction
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Rat.Cast.Defs

/-! # The genus-two source-curve factor of a surface localization vertex

Two tangent directions supply Hodge classes, and each incident flag supplies a
cotangent series. The dimension selects a finite antidiagonal of flag powers.
The marked descendants precede the flag powers in the Hodge integral.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoLocalizationVertex
open GenusTwoVertexHodgeReduction
noncomputable section
variable {K L : Type*} [Field K] [Field L]

/-- Flag powers left by the two Hodge indices and the ordered marked descendants. -/
def profiles (f : ℕ) (m : List ℕ) (i j : Fin 3) : Finset (Fin f → ℕ) :=
  let dim := 3 + m.length + f
  let used := m.sum + (i.val + j.val)
  if used ≤ dim then Finset.finAntidiagonal f (dim - used) else ∅

/-- The truncation retains exactly the top-degree terms, including valence zero. -/
theorem mem_profiles {f : ℕ} (m : List ℕ) (i j : Fin 3) (k : Fin f → ℕ) :
    k ∈ profiles f m i j ↔ m.sum + (i.val + j.val) + ∑ s, k s = 3 + m.length + f := by
  dsimp only [profiles]
  split <;> simp only [Finset.mem_finAntidiagonal, Finset.notMem_empty, false_iff] <;> omega

/-- The signed surface vertex before multiplying the separate tangent normalization.
The coefficient table receives the two λ indices in increasing order. -/
def source (H : (i j : Fin 3) → i ≤ j → List ℕ → ℚ) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) : K :=
  ∑ j : Fin 3, ∑ i : Fin 3, ∑ k ∈ profiles f m i j,
    (((-1 : ℚ)^(i.val+j.val) *
      H (min i j) (max i j) min_le_max (m ++ List.ofFn k) : ℚ) : K) *
      (u^((1 : ℤ)-i.val) * v^((1 : ℤ)-j.val) *
        ∏ s, (flag s)^(-(k s : ℤ)-1))

/-- Any change of character coordinates acts on every flag and both target tangent directions. -/
theorem map_source (φ : K →+* L) (H) {f : ℕ} (m : List ℕ)
    (u v : K) (flag : Fin f → K) :
    φ (source H m u v flag) = source H m (φ u) (φ v) (fun s ↦ φ (flag s)) := by
  simp only [source, map_sum, map_mul, map_ratCast, map_zpow₀, map_prod]

/-- Swapping the two tangent directions reindexes the ordered Hodge indices. -/
theorem swap (H) {f : ℕ} (m : List ℕ) (u v : K) (flag : Fin f → K) :
    source H m u v flag = source H m v u flag := by
  unfold source
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show profiles f m i j = profiles f m j i by simp only [profiles, Nat.add_comm i.val j.val]]
  apply Finset.sum_congr rfl
  intro k _
  simp only [min_comm i j, max_comm i j, Nat.add_comm i.val j.val]
  ac_rfl

/-- The eight Hodge seeds give the numerical source factor for every number of flags and marks. -/
def reduced (seed : ↥seeds → ℚ) {f : ℕ} (m : List ℕ) (u v : K)
    (flag : Fin f → K) : K :=
  source (evaluate seed) m u v flag

/-- A Hodge theory satisfying grading, relabeling, string and dilaton and the declared seed
values has exactly the reduced vertex factor, term by term at every valence. -/
theorem reduced_eq_source (seed : ↥seeds → ℚ) (H : (i j : Fin 3) → i ≤ j → List ℕ → ℚ)
    (laws : ∀ (i j : Fin 3) (h : i ≤ j), Recurrences i j (H i j h))
    (hseed : ∀ (i j : Fin 3) (h : i ≤ j), ∀ p (hk : ((i : ℕ), (j : ℕ), p) ∈ seeds),
      seed ⟨_, hk⟩ = H i j h p) {f : ℕ} (m : List ℕ) (u v : K)
    (flag : Fin f → K) : reduced seed m u v flag = source H m u v flag := by
  unfold reduced source
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have h : min i j ≤ max i j := min_le_max
  rw [evaluate_sound seed _ _ h _ (laws _ _ h) (hseed _ _ h)]

end
end AxiomaticGW.GKM.GenusTwoLocalizationVertex
