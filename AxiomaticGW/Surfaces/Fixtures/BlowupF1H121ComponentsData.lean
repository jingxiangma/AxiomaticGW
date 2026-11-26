/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoResidualPointCache
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CertifiedPoints

/-!
# Full F1 component keys for the original held L24 term 121

Every candidate value remains untrusted until its explicit kernel check.
Component labels use sortCode: unit=0, H=1, E0=2, point=3.
Selector observation-log SHA256: d8b50f7e8ec84f6e3ace9671fdf99440d1c315d4b3e8499f60b57f75c88ddb60
Candidate input SHA256: 378c173898f3fc8df177d98bc64f66e7236b40c466df177f998602b0b0f79e7f
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1H121Components
open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)

def key (i : Fin 48) : SurfaceAncestorKey .hirzebruchOne :=
  (#[
    ⟨0, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![0, 1],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![0, 1],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![1, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![1, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![1, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![1, 0],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![1, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨0, ![1, 1],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.hyperplane, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 0],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![0, 1],
      ([
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.unit, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 0],
      ([
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 1],
      ([
        ⟨.hyperplane, 0⟩,
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    ⟨1, ![1, 1],
      ([
        ⟨.hyperplane, 1⟩,
        ⟨.exceptional 0, 0⟩,
        ⟨.point, 0⟩,
        ⟨.point, 0⟩
      ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩
  ] : Array (SurfaceAncestorKey .hirzebruchOne))[i.val]

def value (i : Fin 48) : ℚ :=
  (#[
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ)
  ] : Array ℚ)[i.val]

def entries (i : Fin 48) : RationalTerms (SurfaceAncestorKey .hirzebruchOne) :=
  RationalTerms.term (value i) 0

end AxiomaticGW.BlowupF1H121Components
