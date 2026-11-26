/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.ComponentStep
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHComponents

/-! # Checked component entries for the two-point blowup

The notation in the finite tables records complete ordered curve coordinates
and a multiset of paired surface states and cotangent powers.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupComponents
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache

abbrev X := SurfaceTarget.blowupTwo
abbrev z : X.Curve := ![0, 0, 0]
abbrev e₁ : X.Curve := ![1, 0, 0]
abbrev e₂ : X.Curve := ![0, 1, 0]
abbrev l : X.Curve := ![0, 0, 1]

/-- Stability is checked at the specified arity for every complete vertex. -/
def componentKey (g : ℕ) (beta : X.Curve) (marks : List (SurfaceInsertion X))
    (hs : 3 ≤ 2 * g + marks.length := by decide) : SurfaceAncestorKey X :=
  ⟨g, beta, marks, by simpa only [Multiset.coe_card] using hs⟩

abbrev u₀ : SurfaceInsertion X := ⟨.unit, 0⟩
abbrev u₁ : SurfaceInsertion X := ⟨.unit, 1⟩
abbrev u₂ : SurfaceInsertion X := ⟨.unit, 2⟩
abbrev h₀ : SurfaceInsertion X := ⟨.hyperplane, 0⟩
abbrev h₁ : SurfaceInsertion X := ⟨.hyperplane, 1⟩
abbrev a₀ : SurfaceInsertion X := ⟨.exceptional 0, 0⟩
abbrev a₁ : SurfaceInsertion X := ⟨.exceptional 0, 1⟩
abbrev b₀ : SurfaceInsertion X := ⟨.exceptional 1, 0⟩
abbrev b₁ : SurfaceInsertion X := ⟨.exceptional 1, 1⟩
abbrev p₀ : SurfaceInsertion X := ⟨.point, 0⟩
abbrev p₁ : SurfaceInsertion X := ⟨.point, 1⟩

/-- Discharge a first-power entry by the dimension-pruned coordinate recursion. -/
def boundedEntry (q : SurfaceAncestorKey X) (value : ℚ)
    (h : value = boundValue X q := by decide +kernel) : Entry X :=
  ⟨q, value, h.trans (boundValue_eq X q)⟩

/-- Reuse a matching component already certified in the original strict-line BP calculation. -/
def lineEntry (q : SurfaceAncestorKey X) (value : ℚ)
    (h : value = BlowupTwoLineH.Components.cached q := by decide +kernel) : Entry X := by
  refine ⟨q, value, h.trans ?_⟩
  rw [BlowupTwoLineH.Components.cached_eq, scalarComponentValue_eq, coordinateComponent_eq]

/-- Replay one boundary against the previous complete-key lookup. -/
def stepEntry (previous : SurfaceAncestorKey X → ℚ)
    (hprevious : ∀ q, previous q = pointCoordinateComponent X q) (q : SurfaceAncestorKey X)
    (value : ℚ) (h : value = stagedValue previous q := by decide +kernel) : Entry X :=
  ⟨q, value, h.trans (stagedValue_eq hprevious q)⟩

end AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupComponents
