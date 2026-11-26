/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveSquareComponents
public import AxiomaticGW.Surfaces.ScalarAncestorFuel

/-! # Reusing checked lower-genus vertices in the two-marked square

The lookup selects a short list of possible entries. A hit requires equality
of the complete ancestor key. The unlisted keys keep the scalar recursion.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoPositiveSquare
open SurfaceLowGenusPointCache SurfacePointBenchmarkCache
variable {X : SurfaceTarget}

/-- A checked lower-genus value including genus, full curve class and marked powers. -/
structure Entry (X : SurfaceTarget) where
  key : SurfaceAncestorKey X
  value : ℚ
  checked : value = coordinateComponent X (genusZero X) (genusOne X) key

/-- A multiset-invariant index used only to select possible matching keys. -/
def slot (q : SurfaceAncestorKey X) : ℕ :=
  (77 * q.genus + (∑ i, 17 ^ (i.val + 1) * q.beta i) +
    (q.insertions.map (fun a ↦ 11 ^ (a.label.sortCode + 10 * a.psi))).sum) % 47

def lookup (q : SurfaceAncestorKey X) : List (Entry X) → ℚ
  | [] => coordinateComponent X (genusZero X) (genusOne X) q
  | e :: rest => if q = e.key then e.value else lookup q rest

private theorem lookup_eq (q : SurfaceAncestorKey X) (rows : List (Entry X)) :
    lookup q rows = coordinateComponent X (genusZero X) (genusOne X) q := by
  induction rows with
  | nil => rfl
  | cons e rest ih =>
    by_cases h : q = e.key
    · rw [lookup, if_pos h, h, e.checked]
    · rw [lookup, if_neg h, ih]

/-- Only the lower-genus scalar evaluation uses the supplied checked entries. -/
def cachedComponent (pool : ℕ → List (Entry X)) (next : SurfaceAncestorKey X → ℚ) :
    SurfaceVertexValues X ℚ :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q.DimensionCompatible then
      if g ≤ 1 then lookup q (pool (slot q)) else next q
    else 0

theorem cachedComponent_eq (pool : ℕ → List (Entry X)) (next : SurfaceAncestorKey X → ℚ) :
    cachedComponent pool next = component next := by
  funext g S inst h beta k a
  simp only [cachedComponent, component, lookup_eq, coordinateComponent_eq, scalarComponentValue_eq]

end AxiomaticGW.SurfaceGenusTwoPositiveSquare
