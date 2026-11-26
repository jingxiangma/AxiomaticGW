/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BasicStrata
public import AxiomaticGW.Tautological.StrataModule
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Finite forgetting of a kappa-decorated corolla

This operation has no old psi insertions. Its distinguished forgotten psi
power is `b + 1`, where the kappa index `b` is positive, so every output index
is positive as required by the existing decorated-graph syntax. The operation
is a finite sum of existing corollas, not a deterministic `StrataOperation`.

The coefficients expand each upstairs kappa as its pulled-back kappa plus a
new-marking psi power. Proper projection then replaces the resulting new psi
power by its kappa generator. This is the stable-vertex branch of admcycles'
`decstratum.forgetful_pushforward`; repeated kappa factors retain their
binomial multiplicities. These definitions alone assert no geometric
realization compatibility or multiplicativity of a strata realization.
-/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.CorollaForgetful

open scoped BigOperators

/-- Retained kappa exponents have the binomial multiplicity of their choices
among the repeated upstairs factors. -/
noncomputable def multiplicity (α β : ℕ+ →₀ ℕ) : ℕ :=
  ∏ i ∈ α.support, Nat.choose (α i) (β i)

/-- The forgotten psi exponent, minus one, includes the weights of every
kappa factor assigned to the new marking. Positivity follows from `b`. -/
noncomputable def mergedIndex (b : ℕ+) (α β : ℕ+ →₀ ℕ) : ℕ+ :=
  ⟨(b : ℕ) + Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) (α - β),
    by exact lt_of_lt_of_le b.property (Nat.le_add_right _ _)⟩

/-- Actual upstairs input: arbitrary positive kappa monomial, no old psi
powers, and a forgotten psi power at least two. -/
noncomputable def source (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (α : ℕ+ →₀ ℕ) (b : ℕ+) :
    TautologicalStratum g (Option S) :=
  TautologicalStratum.oneVertex g (Option S) h.option α
    (fun t ↦ match t with | none => (b : ℕ) + 1 | some _ => 0)

/-- A finite corolla pushforward candidate constructed by binomial kappa
substitution. The interval includes every `β ≤ α`, including both endpoints. -/
noncomputable def push (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (α : ℕ+ →₀ ℕ) (b : ℕ+) : StrataModule g S :=
  ∑ β ∈ Finset.Iic α, (multiplicity α β : ℚ) •
    StrataModule.basis (TautologicalStratum.oneVertex g S h
      (β + Finsupp.single (mergedIndex b α β) 1) (fun _ ↦ 0))


/-- The empty retained vector has binomial multiplicity one. -/
theorem multiplicity_zero (α : ℕ+ →₀ ℕ) : multiplicity α 0 = 1 := by
  simp only [multiplicity, Finsupp.zero_apply, Nat.choose_zero_right,
    Finset.prod_const_one]

/-- Retaining every kappa factor has binomial multiplicity one. -/
theorem multiplicity_self (α : ℕ+ →₀ ℕ) : multiplicity α α = 1 := by
  simp only [multiplicity, Nat.choose_self, Finset.prod_const_one]

/-- If every kappa factor is retained, only the original new psi index remains. -/
theorem mergedIndex_self (b : ℕ+) (α : ℕ+ →₀ ℕ) : mergedIndex b α α = b := by
  apply Subtype.ext
  simp only [mergedIndex, tsub_self, map_zero, Nat.add_zero]
  rfl

/-- Assigning one kappa factor to the new marking adds its positive index. -/
theorem mergedIndex_single_zero (a b : ℕ+) :
    mergedIndex b (Finsupp.single a 1) 0 = a + b := by
  apply Subtype.ext
  simp only [mergedIndex, tsub_zero, Finsupp.weight_single, one_smul]
  exact Nat.add_comm _ _

private theorem Iic_zero : Finset.Iic (0 : ℕ+ →₀ ℕ) = {0} := by
  ext β
  simp only [Finset.mem_Iic, le_zero_iff, Finset.mem_singleton]

/-- A single occurrence can only be assigned wholly to one of the two terms. -/
theorem Iic_single_one (a : ℕ+) :
    Finset.Iic (Finsupp.single a 1 : ℕ+ →₀ ℕ) = {0, Finsupp.single a 1} := by
  ext β
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hβ
    have ha : β a ≤ 1 := by simpa only [Finsupp.single_eq_same] using hβ a
    have hother (i : ℕ+) (hi : i ≠ a) : β i = 0 := by
      have hi' := hβ i
      rw [Finsupp.single_eq_of_ne hi] at hi'
      exact Nat.eq_zero_of_le_zero hi'
    by_cases hz : β a = 0
    · left
      ext i
      by_cases hi : i = a
      · subst i
        exact hz
      · exact hother i hi
    · right
      ext i
      by_cases hi : i = a
      · subst i
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne hi]
        exact hother i hi
  · rintro (rfl | rfl)
    · exact zero_le
    · exact le_rfl

/-- Forgetting a pure new-marking psi power produces the existing generator. -/
theorem push_zero (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (b : ℕ+) :
    push g S h 0 b = StrataModule.basis
      (TautologicalStratum.oneVertex g S h (Finsupp.single b 1) (fun _ ↦ 0)) := by
  rw [push, Iic_zero, Finset.sum_singleton, multiplicity_zero, mergedIndex_self]
  simp only [Nat.cast_one, one_smul, zero_add]

/-- The two-term formula retains both assignments of an arbitrary single
positive kappa factor, even when its index coincides with the new index. -/
theorem push_single (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (a b : ℕ+) :
    push g S h (Finsupp.single a 1) b =
      StrataModule.basis (TautologicalStratum.oneVertex g S h
        (Finsupp.single a 1 + Finsupp.single b 1) (fun _ ↦ 0)) +
      StrataModule.basis (TautologicalStratum.oneVertex g S h
        (Finsupp.single (a + b) 1) (fun _ ↦ 0)) := by
  have hz : (0 : ℕ+ →₀ ℕ) ≠ Finsupp.single a 1 := by
    intro heq
    have he := congrArg (fun f : ℕ+ →₀ ℕ ↦ f a) heq
    rw [Finsupp.zero_apply, Finsupp.single_eq_same] at he
    exact Nat.zero_ne_one he
  rw [push, Iic_single_one, Finset.sum_pair hz, multiplicity_zero,
    multiplicity_self, mergedIndex_single_zero, mergedIndex_self]
  simp only [Nat.cast_one, one_smul, zero_add]
  exact add_comm _ _

/-- The weight API agrees with the kappa codimension used by existing graphs. -/
theorem weight_eq_sum (α : ℕ+ →₀ ℕ) :
    Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) α = α.sum (fun i n ↦ (i : ℕ) * n) := by
  rw [Finsupp.weight_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul, Nat.mul_comm]

/-- Each finite output term has exactly one less codimension than its source. -/
theorem output_codimension (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (α β : ℕ+ →₀ ℕ) (b : ℕ+) (hβ : β ≤ α) :
    (TautologicalStratum.oneVertex g S h
      (β + Finsupp.single (mergedIndex b α β) 1) (fun _ ↦ 0)).codimension =
      Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) α + (b : ℕ) := by
  have hsplit := congrArg (Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)))
    (add_tsub_cancel_of_le hβ)
  rw [map_add] at hsplit
  rw [TautologicalStratum.oneVertex_codimension, Finset.sum_const_zero,
    Nat.add_zero, ← weight_eq_sum, map_add, Finsupp.weight_single, one_smul]
  change Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) β +
      ((b : ℕ) + Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) (α - β)) = _
  omega

/-- The whole finite pushforward is homogeneous in its expected degree. -/
theorem push_mem_degree (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (α : ℕ+ →₀ ℕ) (b : ℕ+) :
    push g S h α b ∈ StrataModule.degree
      (Finsupp.weight (fun i : ℕ+ ↦ (i : ℕ)) α + (b : ℕ)) := by
  classical
  unfold push
  apply Submodule.sum_mem
  intro β hβ
  apply Submodule.smul_mem
  have hc := output_codimension g S h α β b (Finset.mem_Iic.mp hβ)
  exact hc ▸ StrataModule.basis_mem_degree _

end AxiomaticGW.CorollaForgetful
