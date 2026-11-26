/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusOneF1Table

/-!
# Certified F1 point values for the capped blowup diagnostic

Use the existing complete primary tables only at their proved bound.
Beyond that bound the original evaluator remains explicit. These are exact
global replacements of the original point functions, not additional seeds.
This scratch consumer avoids importing unrelated benchmark targets while
their existing build is still running.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1CertifiedPoints

def rational (beta : SurfaceTarget.hirzebruchOne.Curve) : ℚ :=
  if SurfaceTarget.hirzebruchOne.effective.energy beta ≤ 12 then
    GenusZeroF1Table.values beta
  else SurfaceGenusZero.pointValue .hirzebruchOne beta

theorem rational_eq : rational = SurfaceGenusZero.pointValue .hirzebruchOne := by
  funext beta
  unfold rational
  split_ifs with h
  · exact SurfaceGenusZero.checkBoundedValues_sound .hirzebruchOne 12
      GenusZeroF1Table.values GenusZeroF1Table.accepted beta h
  · rfl

def elliptic (beta : SurfaceTarget.hirzebruchOne.Curve) : ℚ :=
  if SurfaceTarget.hirzebruchOne.effective.energy beta ≤ 12 then
    GenusOneF1Table.values beta
  else SurfaceGenusOne.pointValue .hirzebruchOne beta

theorem elliptic_eq : elliptic = SurfaceGenusOne.pointValue .hirzebruchOne := by
  funext beta
  unfold elliptic
  split_ifs with h
  · exact SurfaceGenusOne.checkBoundedValues_sound .hirzebruchOne 12
      GenusZeroF1Table.values GenusOneF1Table.values GenusOneF1Table.accepted beta h
  · rfl

theorem rational_exceptional : rational ![1, 0] = 1 := by decide +kernel

theorem elliptic_cubic : elliptic ![3, 3] = 1 := by decide +kernel

theorem rational_outside (beta : SurfaceTarget.hirzebruchOne.Curve)
    (h : 12 < SurfaceTarget.hirzebruchOne.effective.energy beta) :
    rational beta = SurfaceGenusZero.pointValue .hirzebruchOne beta :=
  if_neg (Nat.not_le.mpr h)

theorem elliptic_outside (beta : SurfaceTarget.hirzebruchOne.Curve)
    (h : 12 < SurfaceTarget.hirzebruchOne.effective.energy beta) :
    elliptic beta = SurfaceGenusOne.pointValue .hirzebruchOne beta :=
  if_neg (Nat.not_le.mpr h)

end AxiomaticGW.BlowupF1CertifiedPoints
