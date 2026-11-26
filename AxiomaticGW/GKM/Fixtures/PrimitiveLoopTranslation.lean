/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SemisimpleCalibration

/-!
# The linear loop coefficient of the primitive-degree resolvent

At distinct fixed points the Taylor coefficient at zero is fixed by the
native two-point tensor and the anticanonical spectral gap. The diagonal is
determined once the coefficient of the flat-unit translation is supplied.
The construction is in the square-zero Novikov ideal with zero classical
loop coefficient. The linear polynomial realizes the first off-diagonal
Taylor coefficient. Higher Taylor powers can already be nonzero at the
same primitive curve degree.
-/

@[expose] public section
namespace AxiomaticGW.GKM.PrimitiveLoopTranslation
open Matrix EquivariantCoefficients SemisimpleCalibration EquivariantCalibrationReplay
open BlowupQuantumIdempotents (Index Direction)
noncomputable section

/-- The forced Taylor entries, using zero as a temporary diagonal. -/
def offDiagonal (X : SurfaceTarget) (d : Direction X) : Matrix (Index X) (Index X) Coefficient :=
  fun i j ↦ if i = j then 0 else -fixedOperator X 0 d i j / (gap X d i j)^2

/-- Complete the diagonal using the specified coefficient of the flat-unit translation at z². -/
def withTranslation (X : SurfaceTarget) (d : Direction X) (u : Index X → Coefficient) :
    Matrix (Index X) (Index X) Coefficient :=
  offDiagonal X d + diagonal (u - offDiagonal X d *ᵥ 1)

/-- Its off-diagonal Taylor entries and flat-unit translation jointly characterize the matrix. -/
theorem eq_iff (X : SurfaceTarget) (d : Direction X) (u : Index X → Coefficient)
    (B : Matrix (Index X) (Index X) Coefficient) :
    B = withTranslation X d u ↔
      (∀ i j, i ≠ j → B i j = -fixedOperator X 0 d i j / (gap X d i j)^2) ∧ B *ᵥ 1 = u := by
  constructor
  · rintro rfl
    constructor
    · intro i j hij
      simp only [withTranslation, Matrix.add_apply, diagonal_apply_ne _ hij, add_zero,
        offDiagonal, if_neg hij]
    · rw [withTranslation, CalibrationSpectrum.translation_shift, add_sub_cancel]
  · rintro ⟨hoff, hu⟩
    have hB : B = offDiagonal X d + diagonal (fun i ↦ B i i) := by
      funext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.add_apply, offDiagonal, ↓reduceIte, diagonal_apply_eq, zero_add]
      · simp only [Matrix.add_apply, diagonal_apply_ne _ hij, add_zero, offDiagonal, if_neg hij,
          hoff i j hij]
    have hdiag := congrArg (fun M ↦ M *ᵥ (1 : Index X → Coefficient)) hB
    rw [CalibrationSpectrum.translation_shift, hu] at hdiag
    have he : (fun i ↦ B i i) = u - offDiagonal X d *ᵥ 1 := by rw [hdiag, add_sub_cancel_left]
    exact hB.trans (congrArg (fun c ↦ offDiagonal X d + diagonal c) he)

/-- Self-adjointness uses the reciprocal Euler metric and the symmetry of the native primary. -/
theorem selfAdjoint (X : SurfaceTarget) (d : Direction X) (u : Index X → Coefficient) :
    diagonal (fun i ↦ ((request X).euler i)⁻¹) * withTranslation X d u =
      (withTranslation X d u).transpose * diagonal (fun i ↦ ((request X).euler i)⁻¹) := by
  funext i j
  simp only [diagonal_mul, mul_diagonal, transpose_apply]
  by_cases hij : i = j
  · subst j
    exact mul_comm _ _
  have hji : j ≠ i := Ne.symm hij
  simp only [withTranslation, Matrix.add_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ hji,
    add_zero, offDiagonal, if_neg hij, if_neg hji]
  simpa only [CalibrationSpectrum.taylorCoefficient, Nat.reduceAdd, neg_one_sq, one_mul,
    mul_comm ((request X).euler j)⁻¹] using (taylor_sewing X d hij 1).symm

open FirstOrderFixedPoints

/-- The square-zero Novikov ideal keeps a separate coordinate for each primitive curve. -/
def coefficient (X : SurfaceTarget) (u : Direction X → Index X → Coefficient) :
    Matrix (Index X) (Index X) (Scalars Coefficient (Direction X)) :=
  fun i j ↦ TrivSqZeroExt.inr (fun d ↦ withTranslation X d (u d) i j)

/-- The assembled matrix is self-adjoint for the actual Gram matrix of the lifted projectors. -/
theorem gram_selfAdjoint (X : SurfaceTarget) (u : Direction X → Index X → Coefficient) :
    (presentation X).gram * coefficient X u =
      (coefficient X u).transpose * (presentation X).gram := by
  let S := presentation X
  have hgram : S.gram = diagonal (norm S.request.euler S.pairs S.weights) := by
    funext i j
    exact S.projector_metric i j
  change S.gram * _ = _ * S.gram
  rw [hgram, S.selfAdjoint_iff]
  intro i j
  apply TrivSqZeroExt.ext
  · simp only [coefficient, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, mul_zero, zero_mul]
  funext d
  have h := congrFun (congrFun (selfAdjoint X d (u d)) i) j
  simp only [diagonal_mul, mul_diagonal, transpose_apply] at h
  simpa only [coefficient, norm, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_mk, op_smul_eq_smul, zero_smul, add_zero,
    zero_add, Pi.smul_apply, smul_eq_mul, S, request_eq,
    mul_comm (withTranslation _ _ _ j i)] using h

/-- The opposite-parameter polynomial is the two-sided inverse over the square-zero ring. -/
theorem inverse (X : SurfaceTarget) (u : Direction X → Index X → Coefficient)
    (z : Scalars Coefficient (Direction X)) :
    (1 + z • coefficient X u) * (1 - z • coefficient X u) = 1 ∧
      (1 - z • coefficient X u) * (1 + z • coefficient X u) = 1 := by
  have hs : coefficient X u * coefficient X u = 0 := by
    funext i j
    simp only [Matrix.mul_apply, coefficient, TrivSqZeroExt.inr_mul_inr, Finset.sum_const_zero,
      Matrix.zero_apply]
  constructor
  · simpa only [hs, smul_zero, sub_zero] using CalibrationSpectrum.inverse_first_loop
      (coefficient X u) z
  · simpa only [neg_smul, ← sub_eq_add_neg, sub_neg_eq_add, hs, smul_zero, sub_zero] using
      CalibrationSpectrum.inverse_first_loop (coefficient X u) (-z)

/-- The actual translation z(1 − R⁻¹)1 packages the prescribed vector on each curve. -/
theorem flat_unit_translation (X : SurfaceTarget) (u : Direction X → Index X → Coefficient)
    (z : Scalars Coefficient (Direction X)) :
    z • ((1 - (1 - z • coefficient X u)) *ᵥ 1) =
      z^2 • (fun i ↦ TrivSqZeroExt.inr (fun d ↦ u d i)) := by
  have hu : coefficient X u *ᵥ 1 = fun i ↦ TrivSqZeroExt.inr (fun d ↦ u d i) := by
    funext i
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one, coefficient, ← TrivSqZeroExt.inr_sum]
    congr 1
    funext d
    have h := congrFun (((eq_iff X d (u d) _).mp rfl).2) i
    simpa only [Finset.sum_apply, mulVec, dotProduct, Pi.one_apply, mul_one] using h
  rw [sub_sub_cancel, smul_mulVec, hu, smul_smul, sq]

/-- The primitive-square-zero loop preserves the projector metric at opposite loop parameters. -/
theorem symplectic (X : SurfaceTarget) (u : Direction X → Index X → Coefficient)
    (z : Scalars Coefficient (Direction X)) :
    (1 - z • coefficient X u).transpose * (presentation X).gram * (1 + z • coefficient X u) =
      (presentation X).gram := by
  let B := coefficient X u
  let G := (presentation X).gram
  have hi := (inverse X u z).2
  have hg : B.transpose * G = G * B := (gram_selfAdjoint X u).symm
  change (1 - z • B).transpose * G * (1 + z • B) = G
  rw [transpose_sub, transpose_one, transpose_smul, sub_mul, one_mul, Matrix.smul_mul, hg,
    ← Matrix.mul_smul, ← mul_one_sub, Matrix.mul_assoc, hi, mul_one]

end
end AxiomaticGW.GKM.PrimitiveLoopTranslation
