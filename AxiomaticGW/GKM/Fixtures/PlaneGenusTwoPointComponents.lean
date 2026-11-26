/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoCachedAncestors

/-!
# Certified components of the plane point ancestor equation

The full degree-one genus-two point ancestor of power three uses these
21 distinct lower-genus components. Every stored expression is checked
against the original algorithm; unlisted components retain that algorithm.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoPointComponents
open SurfaceGenusTwo

/-- Full lower-genus keys, retaining insertion multiplicities and the curve class. -/
def key (i : Fin 21) : SurfaceAncestorKey .plane :=
  (#[
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩
  ] : Array (SurfaceAncestorKey .plane))[i.val]

/-- Candidate scalar expressions, accepted only by the computations below. -/
def entries (i : Fin 21) : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.term ((#[
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 6 : ℚ),
    (-1 / 6 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (1 / 8 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 12 : ℚ)
  ] : Array ℚ)[i.val]) 0

/-- Each full component is stored once. -/
theorem keys_injective : Function.Injective key := by decide +kernel

private theorem value_0 : residualTerms (key 0) = entries 0 := by decide +kernel

private theorem value_1 : residualTerms (key 1) = entries 1 := by decide +kernel

private theorem value_2 : residualTerms (key 2) = entries 2 := by decide +kernel

private theorem value_3 : residualTerms (key 3) = entries 3 := by decide +kernel

private theorem value_4 : residualTerms (key 4) = entries 4 := by decide +kernel

private theorem value_5 : residualTerms (key 5) = entries 5 := by decide +kernel

private theorem value_6 : residualTerms (key 6) = entries 6 := by decide +kernel

private theorem value_7 : residualTerms (key 7) = entries 7 := by decide +kernel

private theorem value_8 : residualTerms (key 8) = entries 8 := by decide +kernel

private theorem value_9 : residualTerms (key 9) = entries 9 := by decide +kernel

private theorem value_10 : residualTerms (key 10) = entries 10 := by decide +kernel

private theorem value_11 : residualTerms (key 11) = entries 11 := by decide +kernel

private theorem value_12 : residualTerms (key 12) = entries 12 := by decide +kernel

private theorem value_13 : residualTerms (key 13) = entries 13 := by decide +kernel

private theorem value_14 : residualTerms (key 14) = entries 14 := by decide +kernel

private theorem value_15 : residualTerms (key 15) = entries 15 := by decide +kernel

private theorem value_16 : residualTerms (key 16) = entries 16 := by decide +kernel

private theorem value_17 : residualTerms (key 17) = entries 17 := by decide +kernel

private theorem value_18 : residualTerms (key 18) = entries 18 := by decide +kernel

private theorem value_19 : residualTerms (key 19) = entries 19 := by decide +kernel

private theorem value_20 : residualTerms (key 20) = entries 20 := by decide +kernel

/-- Individually checked values assembled without re-evaluating other entries. -/
theorem computed (i : Fin 21) : residualTerms (key i) = entries i := by
  fin_cases i
  · exact value_0
  · exact value_1
  · exact value_2
  · exact value_3
  · exact value_4
  · exact value_5
  · exact value_6
  · exact value_7
  · exact value_8
  · exact value_9
  · exact value_10
  · exact value_11
  · exact value_12
  · exact value_13
  · exact value_14
  · exact value_15
  · exact value_16
  · exact value_17
  · exact value_18
  · exact value_19
  · exact value_20

/-- The existing cache interface also preserves every unlisted component. -/
def cache : ResidualCache .plane :=
  ResidualCache.ofEntries key entries keys_injective (fun i ↦ (computed i).symm)

end AxiomaticGW.GKM.PlaneGenusTwoPointComponents
