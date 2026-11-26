/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PrimitiveLoopTranslation

/-! # Taylor coefficients of the primitive-degree resolvent and the flat-unit translation

The off-diagonal entry at power `m` comes from the expansion of the native primitive
resolvent at zero. Odd powers allow a diagonal gauge. At even powers the metric forces
each diagonal entry to vanish. A translation vector specifies the row sums in the
unnormalized primitive-projector basis, where the unit has every coordinate equal to one.
-/

@[expose] public section
namespace AxiomaticGW.GKM.PrimitiveTaylorTranslation
open Matrix EquivariantCoefficients SemisimpleCalibration EquivariantCalibrationReplay
open CalibrationSpectrum FirstOrderFixedPoints
open BlowupQuantumIdempotents (Index Direction)
noncomputable section

variable (X : SurfaceTarget)

/-- The native resolvent Taylor entries away from its diagonal poles. -/
def offDiagonal (d : Direction X) (m : ℕ) : Matrix (Index X) (Index X) Coefficient :=
  fun i j ↦ if i = j then 0 else taylorCoefficient (fixedOperator X 0 d i j) (gap X d i j) m

/-- Complete each row to the specified translation vector. -/
def withTranslation (d : Direction X) (m : ℕ) (u : Index X → Coefficient) :
    Matrix (Index X) (Index X) Coefficient :=
  offDiagonal X d m + diagonal (u - offDiagonal X d m *ᵥ 1)

theorem eq_iff (d : Direction X) (m : ℕ) (u : Index X → Coefficient)
    (B : Matrix (Index X) (Index X) Coefficient) :
    B = withTranslation X d m u ↔
      (∀ i j, i ≠ j → B i j = offDiagonal X d m i j) ∧ B *ᵥ 1 = u := by
  constructor
  · rintro rfl
    refine ⟨fun i j hij ↦ ?_, ?_⟩
    · simp only [withTranslation, Matrix.add_apply, diagonal_apply_ne _ hij, add_zero]
    · rw [withTranslation, translation_shift, add_sub_cancel]
  · rintro ⟨hoff, hu⟩
    have hB : B = offDiagonal X d m + diagonal (fun i ↦ B i i) := by
      funext i j
      by_cases h : i = j
      · subst j
        simp only [Matrix.add_apply, offDiagonal, ↓reduceIte, diagonal_apply_eq, zero_add]
      · simp only [Matrix.add_apply, diagonal_apply_ne _ h, add_zero, hoff i j h]
    have hd := congrArg (fun M ↦ M *ᵥ (1 : Index X → Coefficient)) hB
    rw [translation_shift, hu] at hd
    have he : (fun i ↦ B i i) = u - offDiagonal X d m *ᵥ 1 := by rw [hd, add_sub_cancel_left]
    exact hB.trans (congrArg (fun c ↦ offDiagonal X d m + diagonal c) he)

/-- Reciprocal-Euler adjoint with the sign imposed by opposite loop parameters. -/
def SignedAdjoint (m : ℕ) (B : Matrix (Index X) (Index X) Coefficient) : Prop :=
  ∀ i j, ((request X).euler j)⁻¹ * B j i =
    (-1)^(m + 1) * (((request X).euler i)⁻¹ * B i j)

theorem even_diagonal_zero {m : ℕ} (hm : Even m) {B : Matrix (Index X) (Index X) Coefficient}
    (hB : SignedAdjoint X m B) (i : Index X) : B i i = 0 := by
  have h := hB i i
  rw [hm.add_one.neg_one_pow, neg_one_mul] at h
  have hz : ((request X).euler i)⁻¹ * B i i = 0 := by linear_combination h / 2
  have he := (presentation X).euler_ne i
  rw [request_eq] at he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero he)

/-- Odd powers allow every translation. Even powers require the native row sum. -/
def Admissible (d : Direction X) (m : ℕ) (u : Index X → Coefficient) : Prop :=
  Odd m ∨ u = offDiagonal X d m *ᵥ 1

theorem signed_iff (d : Direction X) (m : ℕ) (u : Index X → Coefficient) :
    SignedAdjoint X m (withTranslation X d m u) ↔ Admissible X d m u := by
  constructor
  · intro h
    rcases Nat.even_or_odd m with hm | hm
    · right
      funext i
      have hz := even_diagonal_zero X hm h i
      simpa only [withTranslation, Matrix.add_apply, offDiagonal, ↓reduceIte,
        diagonal_apply_eq, zero_add, Pi.sub_apply, sub_eq_zero] using hz
    · exact Or.inl hm
  · intro hu i j
    by_cases h : i = j
    · subst j
      rcases hu with hm | rfl
      · rw [hm.add_one.neg_one_pow, one_mul]
      · simp only [withTranslation, sub_self, Matrix.add_apply, diagonal_apply_eq,
          Pi.zero_apply, add_zero, offDiagonal, ↓reduceIte, mul_zero]
    · simpa only [withTranslation, Matrix.add_apply, diagonal_apply_ne _ h,
        diagonal_apply_ne _ (Ne.symm h), add_zero, offDiagonal, if_neg h, if_neg (Ne.symm h)]
        using taylor_sewing X d h m

/-- A skew-adjoint completion uses exactly the native row sum and has zero diagonal. -/
theorem even_completion {m : ℕ} (hm : Even m) (d : Direction X) (u : Index X → Coefficient)
    (hu : Admissible X d m u) :
    u = offDiagonal X d m *ᵥ 1 ∧ withTranslation X d m u = offDiagonal X d m := by
  rcases hu with h | rfl
  · exact (Nat.not_odd_iff_even.mpr hm h).elim
  · exact ⟨rfl, by simp only [withTranslation, sub_self, diagonal_zero', add_zero]⟩

/-- An admissible translation determines the unique coefficient with the prescribed entries
and metric sign. -/
theorem existsUnique_iff (d : Direction X) (m : ℕ) (u : Index X → Coefficient) :
    (∃! B, ((∀ i j, i ≠ j → B i j = offDiagonal X d m i j) ∧ B *ᵥ 1 = u) ∧
      SignedAdjoint X m B) ↔ Admissible X d m u := by
  constructor
  · rintro ⟨B, ⟨hB, hs⟩, _⟩
    rw [(eq_iff X d m u B).mpr hB] at hs
    exact (signed_iff X d m u).mp hs
  · intro h
    exact ⟨withTranslation X d m u, ⟨(eq_iff X d m u _).mp rfl, (signed_iff X d m u).mpr h⟩,
      fun B hB ↦ (eq_iff X d m u B).mpr hB.1⟩

theorem first_order (d : Direction X) (u : Index X → Coefficient) :
    withTranslation X d 1 u = PrimitiveLoopTranslation.withTranslation X d u := rfl

/-- Assemble the separate primitive Novikov directions inside their common square-zero ideal. -/
def coefficient (m : ℕ) (u : Direction X → Index X → Coefficient) :
    Matrix (Index X) (Index X) (Scalars Coefficient (Direction X)) :=
  fun i j ↦ TrivSqZeroExt.inr (fun d ↦ withTranslation X d m (u d) i j)

theorem coefficient_unit (m : ℕ) (u : Direction X → Index X → Coefficient) :
    coefficient X m u *ᵥ 1 = fun i ↦ TrivSqZeroExt.inr (fun d ↦ u d i) := by
  funext i
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one, coefficient, ← TrivSqZeroExt.inr_sum]
  congr 1
  funext d
  have h := congrFun (((eq_iff X d m (u d) _).mp rfl).2) i
  simpa only [Finset.sum_apply, mulVec, dotProduct, Pi.one_apply, mul_one] using h

theorem coefficient_mul (m n : ℕ) (u v : Direction X → Index X → Coefficient) :
    coefficient X m u * coefficient X n v = 0 := by
  funext i j
  simp only [Matrix.mul_apply, coefficient, TrivSqZeroExt.inr_mul_inr, Finset.sum_const_zero,
    Matrix.zero_apply]

/-- The metric sign persists for the full Gram matrix of the lifted primitive projectors. -/
theorem gram_signedAdjoint (m : ℕ) (u : Direction X → Index X → Coefficient)
    (hu : ∀ d, Admissible X d m (u d)) :
    (coefficient X m u).transpose * (presentation X).gram =
      ((-1 : Scalars Coefficient (Direction X))^(m + 1)) •
        ((presentation X).gram * coefficient X m u) := by
  let S := presentation X
  have hgram : S.gram = diagonal (norm S.request.euler S.pairs S.weights) := by
    funext i j
    exact S.projector_metric i j
  change _ * S.gram = _ • (S.gram * _)
  rw [hgram]
  funext i j
  simp only [mul_diagonal, diagonal_mul, transpose_apply, Matrix.smul_apply, smul_eq_mul]
  apply TrivSqZeroExt.ext
  · simp only [coefficient, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, mul_zero, zero_mul]
  funext d
  have h := (signed_iff X d m (u d)).mpr (hu d) i j
  simpa only [coefficient, norm, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_neg, TrivSqZeroExt.fst_one, op_smul_eq_smul,
    zero_smul, add_zero, zero_add, mul_zero, Pi.smul_apply, smul_eq_mul, S, request_eq]
    using h

/-- A finite choice of positive loop powers, indexed by their predecessors. -/
def correction (s : Finset ℕ) (u : ℕ → Direction X → Index X → Coefficient)
    (z : Scalars Coefficient (Direction X)) :
    Matrix (Index X) (Index X) (Scalars Coefficient (Direction X)) :=
  ∑ k ∈ s, z^(k + 1) • coefficient X (k + 1) (u (k + 1))

theorem at_zero (s : Finset ℕ) (u : ℕ → Direction X → Index X → Coefficient) :
    1 + correction X s u 0 = 1 := by
  simp only [correction, zero_pow (Nat.succ_ne_zero _), zero_smul, Finset.sum_const_zero, add_zero]

theorem correction_mul (s t : Finset ℕ) (u v : ℕ → Direction X → Index X → Coefficient)
    (z w : Scalars Coefficient (Direction X)) :
    correction X s u z * correction X t v w = 0 := by
  simp only [correction, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    coefficient_mul, smul_zero, Finset.sum_const_zero]

/-- Every finite positive-power polynomial has exact inverse 1 minus its correction. -/
theorem inverse (s : Finset ℕ) (u : ℕ → Direction X → Index X → Coefficient)
    (z : Scalars Coefficient (Direction X)) :
    (1 + correction X s u z) * (1 - correction X s u z) = 1 ∧
    (1 - correction X s u z) * (1 + correction X s u z) = 1 := by
  simp only [add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one,
    correction_mul, sub_zero, add_zero, sub_add_cancel, add_sub_cancel_right, and_self]

/-- The coefficient of z^(m + 1) in the unit translation is precisely the row sum at power m. -/
theorem flat_unit_translation (s : Finset ℕ) (u : ℕ → Direction X → Index X → Coefficient)
    (z : Scalars Coefficient (Direction X)) :
    z • ((1 - (1 - correction X s u z)) *ᵥ 1) =
      ∑ k ∈ s, z^(k + 2) • (fun i ↦ TrivSqZeroExt.inr (fun d ↦ u (k + 1) d i)) := by
  simp only [sub_sub_cancel, correction, Matrix.sum_mulVec, Matrix.smul_mulVec, coefficient_unit,
    Finset.smul_sum, smul_smul, ← pow_succ']

private theorem opposite_gram (s : Finset ℕ) (u : ℕ → Direction X → Index X → Coefficient)
    (hu : ∀ k ∈ s, ∀ d, Admissible X d (k + 1) (u (k + 1) d))
    (z : Scalars Coefficient (Direction X)) :
    (correction X s u (-z)).transpose * (presentation X).gram =
      -((presentation X).gram * correction X s u z) := by
  simp only [correction, transpose_sum, transpose_smul, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gram_signedAdjoint X (k + 1) _ (hu k hk), smul_smul, ← neg_smul]
  congr 1
  rcases Nat.even_or_odd (k + 1) with h | h
  · rw [h.neg_pow, h.add_one.neg_one_pow, mul_neg_one]
  · rw [h.neg_pow, h.add_one.neg_one_pow, mul_one]

/-- Opposite-parameter symplecticity for the finite polynomial in the square-zero Novikov ring. -/
theorem symplectic (s : Finset ℕ) (u : ℕ → Direction X → Index X → Coefficient)
    (hu : ∀ k ∈ s, ∀ d, Admissible X d (k + 1) (u (k + 1) d))
    (z : Scalars Coefficient (Direction X)) :
    (1 + correction X s u (-z)).transpose * (presentation X).gram *
      (1 + correction X s u z) = (presentation X).gram := by
  rw [transpose_add, transpose_one, add_mul, one_mul, opposite_gram X s u hu z,
    ← sub_eq_add_neg, ← mul_one_sub, Matrix.mul_assoc, (inverse X s u z).2, mul_one]

end
end AxiomaticGW.GKM.PrimitiveTaylorTranslation
