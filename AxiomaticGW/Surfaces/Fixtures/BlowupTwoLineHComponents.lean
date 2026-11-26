/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHConstant

/-! # Certified one-cotangent component values used by the Bl₂ line constant

Every entry checks the original component at its full genus, effective class
and multiset of marked insertions. A bucket selects possible matches and
every hit checks the full ancestor key. Other requests use the existing
scalar component evaluator. Bucket collisions do not identify queries.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineH.Components
open SurfaceLowGenusPointCache SurfacePointBenchmarkCache

set_option Elab.async false
set_option maxRecDepth 65536

/-- A stored scalar and its kernel-checked equality at the entire ancestor key. -/
structure Entry where
  key : SurfaceAncestorKey .blowupTwo
  value : ℚ
  checked : value = scalarComponentValue .blowupTwo (genusZero _) (genusOne _) key

def slot (q : SurfaceAncestorKey .blowupTwo) : ℕ :=
  (97 * q.genus + 23 * q.beta 0 + 41 * q.beta 1 + 47 * q.beta 2 +
    (q.insertions.map (fun m ↦ 131 ^ (m.label.sortCode + 5 * m.psi))).sum) % 509

def lookup (q : SurfaceAncestorKey .blowupTwo) : List Entry → ℚ
  | [] => scalarComponentValue .blowupTwo (genusZero _) (genusOne _) q
  | e :: es => if q = e.key then e.value else lookup q es

private theorem lookup_eq (q : SurfaceAncestorKey .blowupTwo) (entries : List Entry) :
    lookup q entries = scalarComponentValue .blowupTwo (genusZero _) (genusOne _) q := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    by_cases h : q = e.key
    · rw [lookup, if_pos h, h, e.checked]
    · rw [lookup, if_neg h, ih]

def bucket0 : Array (List Entry) := #[
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 24), by decide +kernel⟩],
  [⟨⟨0, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket1 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket2 : Array (List Entry) := #[
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket3 : Array (List Entry) := #[
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  []]

def bucket4 : Array (List Entry) := #[
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket5 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket6 : Array (List Entry) := #[
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨0, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  []]

def bucket7 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket8 : Array (List Entry) := #[
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 24), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  []]

def bucket9 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 8), by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  []]

def bucket10 : Array (List Entry) := #[
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket11 : Array (List Entry) := #[
  [],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 8), by decide +kernel⟩]]

def bucket12 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨0, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket13 : Array (List Entry) := #[
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩]]

def bucket14 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩,
         ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩]]

def bucket15 : Array (List Entry) := #[
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 1, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.point, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 1],
       ([⟨.point, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨0, ![1, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, -1, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [],
  [⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
         ⟨.exceptional 1, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![1, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.hyperplane, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 0],
       ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩],
  [⟨⟨1, ![0, 0, 1],
       ([⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, 0, by decide +kernel⟩,
     ⟨⟨1, ![0, 0, 1],
       ([⟨.exceptional 1, 0⟩, ⟨.exceptional 1, 0⟩, ⟨.exceptional 0, 1⟩] :
         List (SurfaceInsertion .blowupTwo)), by decide⟩, (-1 / 12), by decide +kernel⟩],
  [],
  [],
  [],
  []]

/-- Buckets in the order used by the full-key cache lookup. -/
def buckets : Array (Array (List Entry)) :=
  #[bucket0, bucket1, bucket2, bucket3, bucket4, bucket5, bucket6, bucket7,
    bucket8, bucket9, bucket10, bucket11, bucket12, bucket13, bucket14, bucket15]

/-- A partial component backend queried by full ancestor key. -/
def cached (q : SurfaceAncestorKey .blowupTwo) : ℚ :=
  let k := slot q
  lookup q (((buckets[k / 32]?.getD #[])[k % 32]?).getD [])

theorem cached_eq (q : SurfaceAncestorKey .blowupTwo) :
    cached q = scalarComponentValue .blowupTwo (genusZero _) (genusOne _) q :=
  lookup_eq q _

end AxiomaticGW.BlowupTwoLineH.Components
