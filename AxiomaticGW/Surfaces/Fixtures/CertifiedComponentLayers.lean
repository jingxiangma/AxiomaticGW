/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.ComponentStep

/-! # Degree-indexed replay of lower-genus boundary equations

A layer stores checked rational and elliptic ancestors at one total
cotangent degree. All component evaluations are functions of the full
curve coordinate and multiset of marked insertions. On a missing key the
same boundary equation runs with the preceding degree layers.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoPositiveSquare
open SurfaceLowGenusPointCache
variable {X : SurfaceTarget}

/-- A complete computational backend with a proof for every lower-genus key. -/
structure CertifiedComponents (X : SurfaceTarget) where
  value : SurfaceAncestorKey X → ℚ
  sound : ∀ q, value q = pointCoordinateComponent X q

namespace CertifiedComponents

/-- The original point backend with the proven stable-curve dimension guard. -/
def bounded (X : SurfaceTarget) : CertifiedComponents X :=
  ⟨boundValue X, boundValue_eq X⟩

/-- Check an actual boundary equation using the preceding certified evaluations. -/
def entry (c : CertifiedComponents X) (q : SurfaceAncestorKey X) (v : ℚ)
    (h : v = stagedValue c.value q := by decide +kernel) : Entry X :=
  ⟨q, v, h.trans (stagedValue_eq c.sound q)⟩

/-- A new degree layer leaves every other power on the preceding backend. -/
def layer (c : CertifiedComponents X) (degree : ℕ) (pool : ℕ → List (Entry X)) :
    CertifiedComponents X where
  value q := if q.totalPsi = degree then
    stageLookup (stagedValue c.value) q (pool (slot q)) else c.value q
  sound q := by
    split
    · exact stageLookup_eq (stagedValue c.value) (stagedValue_eq c.sound) q _
    · exact c.sound q

/-- Use the certified layers only on the original dimension-compatible low-genus vertices. -/
def vertex (c : CertifiedComponents X) (next : SurfaceAncestorKey X → ℚ) :
    SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q.DimensionCompatible then
      if g ≤ 1 then c.value q else next q
    else 0

theorem vertex_eq (c : CertifiedComponents X) (next : SurfaceAncestorKey X → ℚ) :
    c.vertex next = component next := by
  funext g S inst h beta k a
  simp only [vertex, component, c.sound, pointCoordinateComponent, coordinateComponent_eq,
    scalarComponentValue_eq]

end CertifiedComponents
end AxiomaticGW.SurfaceGenusTwoPositiveSquare
