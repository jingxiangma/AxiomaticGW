/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalAxisTransport

/-! # Controls for the exceptional-axis transport -/

public section
namespace AxiomaticGWTest.GKM.ExceptionalAxisTransport
open AxiomaticGW AxiomaticGW.GKM
open GKM.ExceptionalAxisTransport
open CurveReplay.OneBlowup renaming tables → f1
open CurveReplay.TwoBlowups renaming tables → bl2

/-- Two distinct source edges over the same exceptional curve with opposite orientations. -/
def parallel : FixedGraphSupport f1 2 2 where
  endpoint := ![![0, 1], ![1, 0]]
  image := ![1, 3]
  edgeIndex _ := 2
  cover := ![1, 2]
  incident := by decide +kernel
  connected := by decide +kernel

/-- The transport preserves both covers and their orientations on either exceptional target. -/
theorem parallel_covers (i : Fin 2) :
    let g := ofSizeEquiv i 3 2 2 ⟨parallel, by decide +kernel⟩
    g.val.cover = ![1, 2] ∧ g.val.endpoint = ![![0, 1], ![1, 0]] ∧
      g.val.degree = (3 : ℕ) • SurfaceTarget.blowupTwo.exceptionalCurve i := by
  let g : {G : FixedGraphSupport f1 2 2 // G.degree = (3 : ℕ) •
    SurfaceTarget.hirzebruchOne.exceptionalCurve 0} := ⟨parallel, by decide +kernel⟩
  have h := preserves_covers i 3 g
  exact ⟨h.2.1, h.1, (ofSizeEquiv i 3 2 2 g).property⟩

/-- The pinned hyperplane lifts disagree along the first exceptional curve. -/
theorem first_hyperplane_differs (p : Fin 2) :
    SurfaceFrames.OneBlowup.request.restrictions (![1, 3] p) 1 ≠
      SurfaceFrames.TwoBlowups.request.restrictions (![1, 2] p) 1 := by
  fin_cases p <;> exact EquivariantCoefficients.x_ne_zero.symm

end AxiomaticGWTest.GKM.ExceptionalAxisTransport
