/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroRecursion
public import AxiomaticGW.Surfaces.GenusZeroExpansion

/-!
# Certified compact evaluation of the reconstruction step

The selected WDVV equation is evaluated with its leading variable set to zero.
The existing support theorem proves that every remaining variable has lower
energy. Thus compression and the guard preserve the complete original remainder.
The leading coefficient is computed from the proved uniform formula.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

open SurfacePolynomialReduction

/-- Preserve the selected energy-three request; compress the uniform marked request. -/
def compactReconstructionTerms (X : SurfaceTarget) (beta : X.Curve) :
    RationalTerms (Variable X) :=
  if X.effective.energy beta = 3 then reconstructionTerms X beta else
    WDVV.compactPrimaryTerms X (X.effective.energy beta - 4) beta
      (WDVV.reconstructionLabels X)

/-- Compression preserves all valuations, not merely the requested numerical answer. -/
theorem eval_compactReconstructionTerms {A : Type*} [CommRing A] [Algebra ℚ A]
    {X : SurfaceTarget} (v : Variable X → A) (beta : X.Curve) :
    RationalTerms.eval v (compactReconstructionTerms X beta) =
      RationalTerms.eval v (reconstructionTerms X beta) := by
  unfold compactReconstructionTerms
  split_ifs with hthree
  · rfl
  · rw [WDVV.eval_compactPrimaryTerms, reconstructionTerms,
      reconstructionRequest.eq_def, if_neg hthree]

/-- The uniform coefficient is one; only the unmarked exceptional profile is computed. -/
def compactReconstructionCoefficient (X : SurfaceTarget) (beta : X.Curve) : ℚ :=
  if X.effective.energy beta = 3 then reconstructionCoefficient X beta else 1

theorem compactReconstructionCoefficient_eq (X : SurfaceTarget) (beta : X.Curve)
    (h : ¬IsInitial X beta) :
    compactReconstructionCoefficient X beta = reconstructionCoefficient X beta := by
  unfold compactReconstructionCoefficient
  split_ifs with hthree
  · rfl
  · have he : ¬X.effective.energy beta ≤ 2 := fun he ↦ h (Or.inl he)
    have hfour : 4 ≤ X.effective.energy beta := by omega
    rw [reconstructionCoefficient, reconstructionTerms, reconstructionRequest.eq_def,
      if_neg hthree, WDVV.primaryTerms_reconstruction_coefficient X beta hfour]

/-- A finite compact step using only values of strictly lower-energy variables. -/
def compactReconstructionStep (X : SurfaceTarget) (beta : X.Curve)
    (v : Variable X → ℚ) : ℚ :=
  -RationalTerms.eval
      (fun u ↦ if X.effective.energy (variableCurve u) < X.effective.energy beta then v u else 0)
      (compactReconstructionTerms X beta) / compactReconstructionCoefficient X beta

/-- The guard removes precisely the leading singleton and leaves all dependencies intact. -/
theorem compactReconstructionStep_eq (X : SurfaceTarget) (beta : X.Curve)
    (h : ¬IsInitial X beta) (v : Variable X → ℚ) :
    compactReconstructionStep X beta v =
      -RationalTerms.eval v (reconstructionRemainder X beta) /
        reconstructionCoefficient X beta := by
  let w : Variable X → ℚ := fun u ↦
    if X.effective.energy (variableCurve u) < X.effective.energy beta then v u else 0
  have hz : w (pointVariable X beta) = 0 := if_neg (lt_irrefl _)
  have heval : RationalTerms.eval w (reconstructionTerms X beta) =
      RationalTerms.eval v (reconstructionRemainder X beta) := by
    rw [RationalTerms.eval_isolate_singleton w _ (pointVariable X beta), hz,
      mul_zero, zero_add]
    apply RationalTerms.eval_congr
    intro t ht u hu
    obtain ⟨gamma, _, rfl, hlt⟩ := reconstructionRemainder_dependencies X beta t ht u hu
    exact if_pos hlt
  unfold compactReconstructionStep
  rw [eval_compactReconstructionTerms, compactReconstructionCoefficient_eq X beta h]
  change -RationalTerms.eval w _ / _ = _
  rw [heval]

end AxiomaticGW.SurfaceGenusZero
