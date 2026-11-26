/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests
public import AxiomaticGW.Surfaces.Fixtures.PlaneGenusOneSupport
public import AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate

/-!
# Incoming plane few-marking claims and arithmetic support

Input SHA256: 3b5ce0bba45b34a09832afbc1f93639b4c4eabc69c4b60e35f084f0d845a90a9
Each ordinary value is checked against its complete descendant query.
The literal canonical table is candidate data here. Final replay identifies it
with the existing accepted line table. Lower-genus caches have separate proofs.
This does not certify equivariant localization or import CohFT classes.
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536
set_option cbv.maxSteps 4000000

namespace AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay

open BelorousskiPandharipande

/-- Complete ordered incoming requests, checked against the independent benchmark frame. -/
def requests (i : Fin 48) : SurfaceQuery .plane :=
  (#[⟨2, ![1], [⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 0⟩, ⟨.unit, 6⟩]⟩,
    ⟨2, ![1], [⟨.unit, 1⟩, ⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.unit, 2⟩, ⟨.unit, 4⟩]⟩,
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.unit, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 4⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![1], [⟨.unit, 5⟩, ⟨.unit, 1⟩]⟩,
    ⟨2, ![1], [⟨.unit, 6⟩, ⟨.unit, 0⟩]⟩,
    ⟨2, ![1], [⟨.unit, 0⟩, ⟨.hyperplane, 5⟩]⟩,
    ⟨2, ![1], [⟨.unit, 1⟩, ⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.unit, 2⟩, ⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1], [⟨.unit, 4⟩, ⟨.hyperplane, 1⟩]⟩,
    ⟨2, ![1], [⟨.unit, 5⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨2, ![1], [⟨.unit, 0⟩, ⟨.point, 4⟩]⟩,
    ⟨2, ![1], [⟨.unit, 1⟩, ⟨.point, 3⟩]⟩,
    ⟨2, ![1], [⟨.unit, 2⟩, ⟨.point, 2⟩]⟩,
    ⟨2, ![1], [⟨.unit, 3⟩, ⟨.point, 1⟩]⟩,
    ⟨2, ![1], [⟨.unit, 4⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.unit, 5⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.unit, 4⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 2⟩, ⟨.unit, 3⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 3⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩, ⟨.unit, 1⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 5⟩, ⟨.unit, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.hyperplane, 4⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 2⟩, ⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 3⟩, ⟨.hyperplane, 1⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 4⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 0⟩, ⟨.point, 3⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 1⟩, ⟨.point, 2⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 2⟩, ⟨.point, 1⟩]⟩,
    ⟨2, ![1], [⟨.hyperplane, 3⟩, ⟨.point, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.unit, 4⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.unit, 3⟩]⟩,
    ⟨2, ![1], [⟨.point, 2⟩, ⟨.unit, 2⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩, ⟨.unit, 1⟩]⟩,
    ⟨2, ![1], [⟨.point, 4⟩, ⟨.unit, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.hyperplane, 3⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.hyperplane, 2⟩]⟩,
    ⟨2, ![1], [⟨.point, 2⟩, ⟨.hyperplane, 1⟩]⟩,
    ⟨2, ![1], [⟨.point, 3⟩, ⟨.hyperplane, 0⟩]⟩,
    ⟨2, ![1], [⟨.point, 0⟩, ⟨.point, 2⟩]⟩,
    ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩,
    ⟨2, ![1], [⟨.point, 2⟩, ⟨.point, 0⟩]⟩] : Array (SurfaceQuery .plane))[i.val]

/-- Exact incoming ordinary values; subsequent replay certifies each full claim. -/
def values (i : Fin 48) : ℚ :=
  (#[(1 / 128), (-1 / 960), (-1 / 240), (1 / 128),
    (3 / 128), (19 / 640), (7 / 320), (19 / 640),
    (3 / 128), (1 / 128), (-1 / 960), (-1 / 320),
    (7 / 480), (1 / 30), (13 / 640), (13 / 1920),
    (-1 / 240), (-1 / 80), (-1 / 48), (-23 / 960),
    (-17 / 1920), (13 / 1920), (13 / 640), (1 / 30),
    (7 / 480), (-1 / 320), (-1 / 960), (-1 / 192),
    (-23 / 960), (-29 / 960), (-23 / 960), (-1 / 192),
    (-1 / 240), (-1 / 240), (-1 / 160), (-7 / 960),
    (-17 / 1920), (-23 / 960), (-1 / 48), (-1 / 80),
    (-1 / 240), (-7 / 960), (-1 / 160), (-1 / 240),
    (-1 / 240), (1 / 240), (1 / 144), (1 / 240)] : Array ℚ)[i.val]

/-- Every incoming request matches the independently held full query. -/
theorem coverage : ∀ i, requests i = GenusTwoPlaneFewMarkingRequests.requests i := by
  decide +kernel

/-- Literal canonical candidates; their acceptance is checked in the final assembly. -/
def canonicalValues (d : ℕ) : Fin 3 → ℚ :=
  match d with
  | 0 => ![0, -1 / 960, 0]
  | _ => ![0, 0, 0]

-- Avoid evaluating unused recursive arguments of Fin.cases during cbv.
theorem vectorLookup {α : Type*} {n : ℕ} (x : α) (xs : Fin n → α)
    (i : Fin (n + 1)) : Matrix.vecCons x xs i =
      if h : i.val = 0 then x else xs ⟨i.val - 1, by omega⟩ := by
  rcases i with ⟨i, hi⟩
  cases i <;> rfl

theorem rationalCached (beta : SurfaceTarget.plane.Curve) :
    SurfaceGenusZero.pointValue .plane beta =
      if SurfaceTarget.plane.effective.energy beta ≤ 15
      then PlaneGenusZeroSupport.values beta else SurfaceGenusZero.pointValue .plane beta := by
  split_ifs with h
  · exact (PlaneGenusZeroSupport.values_eq beta h).symm
  · rfl

theorem ellipticCached (beta : SurfaceTarget.plane.Curve) :
    SurfaceGenusOne.pointValue .plane beta =
      if SurfaceTarget.plane.effective.energy beta ≤ 15
      then PlaneGenusOneSupport.values beta else SurfaceGenusOne.pointValue .plane beta := by
  split_ifs with h
  · exact (PlaneGenusOneSupport.values_eq beta h).symm
  · rfl

end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay
