/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.SurfaceEdgeNonvanishing
public import AxiomaticGW.GKM.Fixtures.ExceptionalCoverFactors

/-! # Surface edge evaluation on a curve of self-intersection minus one -/

@[expose] public noncomputable section
namespace AxiomaticGW.GKM.SurfaceEdgeReplay
open CurveConventionCertificate EquivariantCoefficients

/-- Every wall in each of the three pinned fans admits the full edge factor at every
positive covering degree, in the exact two-character field. -/
theorem all_cover_degrees (d : ℕ+) :
    (∀ i, (SurfaceLocalizationEdge.atEdge? CurveReplay.Plane.tables i d).isSome) ∧
    (∀ i, (SurfaceLocalizationEdge.atEdge? CurveReplay.OneBlowup.tables i d).isSome) ∧
    (∀ i, (SurfaceLocalizationEdge.atEdge? CurveReplay.TwoBlowups.tables i d).isSome) := by
  refine ⟨fun i ↦ SurfaceLocalizationEdge.atEdge_isSome _ i d ?_,
    fun i ↦ SurfaceLocalizationEdge.atEdge_isSome _ i d ?_,
    fun i ↦ SurfaceLocalizationEdge.atEdge_isSome _ i d ?_⟩ <;>
    revert i <;> unfold SurfaceLocalizationEdge.Transverse <;> decide +kernel

/-- For a (−1)-curve the general signed-degree formula recovers the original exceptional
obstruction product at every covering degree. -/
theorem negative_one {X : SurfaceTarget} {v e : ℕ} (t : Tables X v e) (i : Fin e)
    (d : ℕ+) (degree : (t.edges i).normalDegree = -1) (weight : character (t.edges i).weight ≠ 0) :
    SurfaceLocalizationEdge.atEdge? t i d = some (ExceptionalCoverFactors.atEdge t i d) := by
  classical
  have pos := d.pos
  have k : (d.val : ℤ) * (-1) = Int.negSucc (d.val - 1) := by omega
  have hf : (d.val.factorial : Coefficient) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [SurfaceLocalizationEdge.atEdge?, SurfaceLocalizationEdge.factor?, weight, hf,
    or_self, if_false,
    degree, k, SurfaceLocalizationEdge.normal?, ExceptionalCoverFactors.atEdge,
    ExceptionalCoverFactors.factor, ExceptionalCoverFactors.normal]
  rfl

end AxiomaticGW.GKM.SurfaceEdgeReplay
