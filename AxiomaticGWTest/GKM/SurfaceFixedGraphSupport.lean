/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SurfaceFixedGraphSupport

/-! # Degree and support controls for the three pinned surface edge tables -/

@[expose] public section
namespace AxiomaticGWTest.GKM.SurfaceFixedGraphSupport
open AxiomaticGW AxiomaticGW.GKM
open FixedGraphSupport (AtDegree)
open GKM.SurfaceFixedGraphSupport (coveredPath twoBlowups_iff)

/-- Empty paths are allowed at the origin of each effective cone. -/
theorem origins : Nonempty (AtDegree CurveReplay.Plane.tables 0) ∧
    Nonempty (AtDegree CurveReplay.OneBlowup.tables 0) ∧
    Nonempty (AtDegree CurveReplay.TwoBlowups.tables 0) := by
  exact ⟨GKM.SurfaceFixedGraphSupport.plane _, GKM.SurfaceFixedGraphSupport.oneBlowup _,
    (twoBlowups_iff _).mpr (Or.inr (Or.inl rfl))⟩

/-- F occurs first along the path, although E is the first full class coordinate. -/
theorem oneBlowup_covers : (coveredPath CurveReplay.OneBlowup.tables ![0, 1, 3]
    ![0, 2] ![5, 2] (by decide +kernel)).degree = ![2, 5] := by decide +kernel

/-- Edges are ordered E₁,L,E₂ on the path, whereas coordinates are E₁,E₂,L. -/
theorem twoBlowups_covers : (coveredPath CurveReplay.TwoBlowups.tables ![1, 2, 3, 4]
    ![2, 3, 4] ![2, 5, 3] (by decide +kernel)).degree = ![2, 3, 5] := by decide +kernel

/-- Equal anticanonical energy can give opposite connectivity answers. -/
theorem equal_energy_different_support :
    SurfaceTarget.blowupTwo.effective.energy ![1, 1, 0] =
      SurfaceTarget.blowupTwo.effective.energy ![1, 0, 1] ∧
    ¬ Nonempty (AtDegree CurveReplay.TwoBlowups.tables ![1, 1, 0]) ∧
    Nonempty (AtDegree CurveReplay.TwoBlowups.tables ![1, 0, 1]) := by
  rw [twoBlowups_iff, twoBlowups_iff]
  decide +kernel

end AxiomaticGWTest.GKM.SurfaceFixedGraphSupport
