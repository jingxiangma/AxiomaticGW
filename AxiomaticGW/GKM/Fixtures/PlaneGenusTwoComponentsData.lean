/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointComponents
public import AxiomaticGW.Surfaces.LowGenusAncestorDimension

/-!
# Shared lower-genus components of the plane ancestor suite

Each candidate value is separately checked against the original residual algorithm.
The symbolic rows only select cache entries; final equations require their own replay.

Candidate input SHA256: 2001e7124121cf35e55daa7984cd86b3ac230a9d711f68b225941c4e7e3dbfc9
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.GKM.PlaneGenusTwoComponents
open SurfaceGenusTwo

/-- Full lower-genus keys, retaining insertion multiplicities and the curve class. -/
def key (i : Fin 291) : SurfaceAncestorKey .plane :=
  (#[
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
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
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
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
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
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
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
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
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
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
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
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
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨0, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩
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
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![0],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
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
    ⟨1, ![0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 5⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 1⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 1⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.point, 1⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 5⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 5⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 5⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
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
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 1⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.unit, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 2⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.unit, 4⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
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
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
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
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
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
        ⟨.unit, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.unit, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.hyperplane, 2⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.hyperplane, 2⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.point, 0⟩,
        ⟨.unit, 3⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.point, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩,
    ⟨1, ![1],
      ([
        ⟨.point, 0⟩,
        ⟨.point, 1⟩
      ] : List (SurfaceInsertion .plane)), by decide⟩
  ] : Array (SurfaceAncestorKey .plane))[i.val]

/-- Candidate scalar expressions, accepted only by the computations below. -/
def entries (i : Fin 291) : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.term ((#[
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (3 / 1 : ℚ),
    (2 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (2 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (2 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (2 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (3 / 1 : ℚ),
    (4 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 1 : ℚ),
    (3 / 1 : ℚ),
    (0 / 1 : ℚ),
    (2 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (3 / 1 : ℚ),
    (6 / 1 : ℚ),
    (3 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (2 / 1 : ℚ),
    (2 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (-1 / 4 : ℚ),
    (3 / 4 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (-1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 2 : ℚ),
    (0 / 1 : ℚ),
    (-5 / 24 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (1 / 24 : ℚ),
    (-1 / 12 : ℚ),
    (3 / 8 : ℚ),
    (-1 / 6 : ℚ),
    (1 / 8 : ℚ),
    (3 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 4 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (-1 / 6 : ℚ),
    (1 / 4 : ℚ),
    (-1 / 12 : ℚ),
    (1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 6 : ℚ),
    (0 / 1 : ℚ),
    (3 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 2 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (3 / 4 : ℚ),
    (-1 / 4 : ℚ),
    (1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (-1 / 4 : ℚ),
    (1 / 4 : ℚ),
    (3 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 4 : ℚ),
    (1 / 4 : ℚ),
    (1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 6 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (3 / 8 : ℚ),
    (5 / 24 : ℚ),
    (-1 / 6 : ℚ),
    (-1 / 24 : ℚ),
    (1 / 8 : ℚ),
    (1 / 6 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (3 / 4 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 4 : ℚ),
    (1 / 4 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (1 / 8 : ℚ),
    (-1 / 12 : ℚ),
    (1 / 8 : ℚ),
    (1 / 4 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 4 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (1 / 8 : ℚ),
    (1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ)
  ] : Array ℚ)[i.val]) 0

end AxiomaticGW.GKM.PlaneGenusTwoComponents
