/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers

/-! # Full-coordinate lower-genus vertices for the F₁ fiber class -/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs.Components

abbrev X := SurfaceTarget.hirzebruchOne
abbrev zeroClass : X.Curve := ![0, 0]
abbrev fiberClass : X.Curve := ![0, 1]
abbrev unit (p : ℕ) : SurfaceInsertion X := ⟨.unit, p⟩
abbrev H (p : ℕ) : SurfaceInsertion X := ⟨.hyperplane, p⟩
abbrev E (p : ℕ) : SurfaceInsertion X := ⟨.exceptional 0, p⟩
abbrev pt (p : ℕ) : SurfaceInsertion X := ⟨.point, p⟩

/-- Stability is checked at the full list of paired state and cotangent insertions. -/
def node (g : ℕ) (beta : X.Curve) (marks : List (SurfaceInsertion X))
    (hs : 3 ≤ 2 * g + marks.length := by decide) : SurfaceAncestorKey X :=
  ⟨g, beta, marks, by simpa only [Multiset.coe_card] using hs⟩

end AxiomaticGW.BlowupF1FiberInteriorPairs.Components
