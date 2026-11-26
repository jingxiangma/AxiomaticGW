/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.EffectiveCurveClass
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Executable weighted effective classes

Finite tuples of natural numbers with positive energy weights model the
effective coordinates of the three fixed surface applications. Bounded
enumeration and splitting are executable, with completeness proved against
`EffectiveCurveMonoid`. No geometric identification is implicit in this model.
-/

@[expose] public section

namespace AxiomaticGW.WeightedCurveClass

variable {n : ℕ}

/-- Additive energy of a tuple of effective generator multiplicities. -/
def energy (w : Fin n → ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun beta := ∑ i, w i * beta i
  map_zero' := by simp only [Pi.zero_apply, Nat.mul_zero, Finset.sum_const_zero]
  map_add' := by
    intro a b
    simp only [Pi.add_apply, Nat.mul_add, Finset.sum_add_distrib]

/-- Positive weights bound every coordinate by the total energy. -/
theorem coordinate_le_energy (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (beta : Fin n → ℕ) (i : Fin n) : beta i ≤ energy w beta := by
  exact (Nat.le_mul_of_pos_left _ (hw i)).trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (w j * beta j)) (Finset.mem_univ i))

/-- Enumerate a finite box and retain exactly the requested energy bound. -/
def bounded (w : Fin n → ℕ) (d : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ ↦ Finset.range (d + 1))).filter (fun beta ↦ energy w beta ≤ d)

theorem mem_bounded (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (d : ℕ) (beta : Fin n → ℕ) : beta ∈ bounded w d ↔ energy w beta ≤ d := by
  rw [bounded, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Fintype.mem_piFinset.mpr (fun i ↦ ?_), h⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((coordinate_le_energy w hw beta i).trans h))

/-- The executable coordinate monoid realizes the existing abstract API. -/
def effective (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    EffectiveCurveMonoid (Fin n → ℕ) where
  energy := energy w
  energy_eq_zero_iff := by
    intro beta
    constructor
    · intro h
      funext i
      exact Nat.eq_zero_of_le_zero (h ▸ coordinate_le_energy w hw beta i)
    · rintro rfl
      exact map_zero (energy w)
  finite_energy_le := by
    intro d
    exact (bounded w d).finite_toSet.subset (fun beta h ↦ (mem_bounded w hw d beta).mpr h)

/-- The executable bounded set equals the abstract finite set. -/
theorem bounded_eq (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (d : ℕ) :
    bounded w d = (effective w hw).bounded d := by
  ext beta
  exact (mem_bounded w hw d beta).trans ((effective w hw).mem_bounded d beta).symm

/-- Enumerate each possible first summand once; subtraction determines the
second. This avoids searching all pairs in a bounded-energy box. -/
def splittings (beta : Fin n → ℕ) : Finset ((Fin n → ℕ) × (Fin n → ℕ)) :=
  (Fintype.piFinset (fun i ↦ Finset.range (beta i + 1))).image
    (fun a ↦ (a, beta - a))

theorem mem_splittings (beta a b : Fin n → ℕ) :
    (a, b) ∈ splittings beta ↔ a + b = beta := by
  rw [splittings, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hpair⟩
    have ha : x = a := congrArg Prod.fst hpair
    have hb : beta - x = b := congrArg Prod.snd hpair
    rw [← ha, ← hb]
    funext i
    have hi := Finset.mem_range.mp (Fintype.mem_piFinset.mp hx i)
    change x i + (beta i - x i) = beta i
    omega
  · intro h
    refine ⟨a, Fintype.mem_piFinset.mpr (fun i ↦ ?_), ?_⟩
    · have hi := congrFun h i
      change a i + b i = beta i at hi
      exact Finset.mem_range.mpr (by omega)
    · apply congrArg (fun x ↦ (a, x))
      funext i
      have hi := congrFun h i
      change a i + b i = beta i at hi
      change beta i - a i = b i
      omega

/-- Executable splitting is complete for the existing Novikov convolution. -/
theorem splittings_eq (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (beta : Fin n → ℕ) :
    splittings beta = (effective w hw).splittings beta := by
  ext pair
  rcases pair with ⟨a, b⟩
  exact (mem_splittings beta a b).trans ((effective w hw).mem_splittings a b beta).symm

end AxiomaticGW.WeightedCurveClass
