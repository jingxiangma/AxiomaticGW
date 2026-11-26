/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoResidualPointCache
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CertifiedPoints

/-!
# Complete selected F1 H-row full component keys and candidate values

Complete request: F1 source [1,1], one added point, H/E0/E0/E0; 721 L24 terms.
These component certificates do not certify the final 721-term contraction.
Full-key labels use sortCode: unit=0, H=1, E0=2, point=3.
Selector observation-log SHA256:
  a5c4c41abad31443bffce2ffd25e3033c4746a82c1ef4ba144644d1e583a82f1
Selector Lean source SHA256:
  9dd879b24ac01f7d32f29e994b43ac9aba2add243b1104879f5dbab9947e7369
Untrusted candidate input SHA256:
  292366499879e648aeb9deaa66c1f33a693d2eadde188eb7639801e33fe9ec1b
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1CompleteHComponents
open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)

def key000 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key001 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key002 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key003 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key004 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key005 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key006 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key007 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key008 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key009 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key010 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key011 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key012 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key013 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key014 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key015 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key016 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key017 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key018 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key019 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key020 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key021 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key022 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key023 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key024 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key025 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key026 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key027 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key028 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key029 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key030 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key031 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key032 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key033 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key034 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key035 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key036 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key037 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key038 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key039 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key040 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key041 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key042 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key043 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key044 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key045 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key046 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key047 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key048 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key049 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key050 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key051 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key052 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key053 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key054 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key055 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key056 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key057 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key058 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key059 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key060 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key061 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key062 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key063 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key064 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key065 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key066 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key067 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key068 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key069 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key070 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key071 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key072 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key073 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key074 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key075 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key076 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key077 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key078 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key079 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key080 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key081 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key082 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key083 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key084 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key085 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key086 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key087 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key088 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key089 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key090 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key091 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key092 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key093 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key094 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key095 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key096 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key097 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key098 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key099 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key100 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key101 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key102 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key103 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key104 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key105 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key106 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key107 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key108 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key109 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key110 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key111 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key112 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key113 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key114 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key115 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key116 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key117 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key118 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key119 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key120 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key121 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key122 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key123 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key124 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key125 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key126 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key127 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key128 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key129 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key130 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key131 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key132 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key133 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key134 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key135 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key136 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key137 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key138 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key139 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key140 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key141 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key142 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key143 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key144 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key145 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key146 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key147 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key148 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key149 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key150 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key151 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key152 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key153 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key154 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key155 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key156 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key157 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key158 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key159 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key160 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key161 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key162 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key163 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key164 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key165 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key166 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key167 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key168 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key169 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key170 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key171 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key172 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key173 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key174 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key175 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key176 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key177 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key178 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key179 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key180 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key181 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key182 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key183 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key184 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key185 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key186 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key187 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key188 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key189 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key190 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key191 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key192 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key193 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key194 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key195 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key196 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key197 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key198 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key199 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key200 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key201 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key202 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key203 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key204 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key205 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key206 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key207 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key208 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key209 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key210 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key211 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key212 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key213 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key214 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key215 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key216 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key217 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key218 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key219 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key220 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key221 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key222 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key223 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key224 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key225 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key226 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key227 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key228 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key229 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key230 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key231 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key232 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key233 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key234 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key235 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key236 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key237 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key238 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key239 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key240 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key241 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key242 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key243 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key244 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key245 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key246 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key247 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key248 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key249 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key250 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key251 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key252 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key253 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key254 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key255 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key256 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key257 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key258 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key259 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key260 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key261 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key262 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key263 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key264 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key265 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key266 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key267 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key268 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key269 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key270 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key271 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key272 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key273 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key274 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key275 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key276 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key277 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key278 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key279 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key280 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key281 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key282 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key283 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key284 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key285 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key286 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key287 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key288 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key289 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key290 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key291 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key292 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key293 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key294 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key295 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key296 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key297 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key298 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key299 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key300 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key301 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key302 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key303 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key304 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key305 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key306 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key307 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key308 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key309 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key310 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key311 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key312 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key313 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key314 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key315 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key316 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key317 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key318 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key319 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key320 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key321 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key322 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key323 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key324 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key325 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key326 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key327 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key328 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key329 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key330 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key331 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key332 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key333 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key334 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key335 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key336 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key337 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key338 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key339 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key340 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key341 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key342 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key343 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key344 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key345 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key346 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key347 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key348 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key349 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key350 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key351 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key352 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key353 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key354 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key355 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key356 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key357 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key358 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key359 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key360 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key361 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key362 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key363 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key364 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key365 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key366 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key367 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key368 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key369 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key370 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key371 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key372 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key373 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key374 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key375 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key376 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key377 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key378 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key379 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key380 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key381 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key382 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key383 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key384 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key385 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key386 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key387 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key388 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key389 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key390 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key391 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key392 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key393 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key394 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨0, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key395 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key396 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key397 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key398 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key399 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key400 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key401 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key402 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key403 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key404 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key405 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key406 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key407 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key408 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key409 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key410 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key411 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key412 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key413 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key414 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key415 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key416 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key417 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key418 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key419 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key420 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key421 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key422 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key423 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key424 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key425 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key426 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key427 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key428 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key429 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key430 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key431 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key432 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key433 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key434 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key435 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key436 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key437 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key438 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key439 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key440 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key441 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key442 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key443 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key444 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key445 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key446 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key447 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key448 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key449 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key450 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key451 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key452 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key453 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key454 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key455 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key456 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key457 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key458 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key459 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key460 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key461 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key462 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key463 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key464 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key465 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key466 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key467 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key468 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key469 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key470 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key471 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key472 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key473 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key474 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key475 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key476 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key477 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key478 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key479 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key480 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key481 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key482 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key483 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key484 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key485 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key486 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key487 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key488 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key489 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key490 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key491 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key492 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key493 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key494 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key495 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key496 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key497 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key498 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key499 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key500 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key501 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key502 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key503 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key504 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key505 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key506 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key507 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key508 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key509 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key510 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key511 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key512 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key513 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key514 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key515 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key516 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key517 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key518 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key519 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key520 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key521 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key522 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key523 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key524 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key525 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key526 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key527 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key528 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key529 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key530 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key531 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key532 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key533 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key534 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key535 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key536 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key537 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key538 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key539 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key540 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key541 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key542 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key543 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key544 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key545 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key546 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key547 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key548 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key549 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key550 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key551 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key552 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key553 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key554 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key555 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key556 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key557 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key558 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key559 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key560 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key561 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key562 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![0, 1],
    ([
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key563 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key564 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key565 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key566 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key567 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key568 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key569 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key570 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key571 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key572 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key573 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key574 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key575 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key576 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key577 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key578 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key579 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key580 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key581 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key582 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key583 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key584 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key585 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key586 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key587 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key588 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key589 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key590 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key591 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key592 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key593 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key594 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key595 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key596 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key597 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key598 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key599 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key600 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key601 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key602 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key603 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key604 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key605 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key606 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key607 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key608 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key609 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key610 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key611 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key612 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key613 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key614 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key615 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key616 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key617 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key618 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key619 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key620 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key621 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key622 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key623 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key624 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.unit, 1⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key625 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key626 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key627 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key628 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key629 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key630 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key631 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key632 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key633 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key634 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key635 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key636 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key637 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key638 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key639 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key640 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key641 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key642 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key643 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key644 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key645 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key646 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key647 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key648 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key649 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key650 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key651 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key652 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key653 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key654 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key655 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key656 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key657 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key658 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key659 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key660 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key661 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key662 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key663 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key664 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key665 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key666 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key667 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.exceptional 0, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key668 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 0],
    ([
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key669 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key670 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key671 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key672 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key673 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key674 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key675 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key676 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key677 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key678 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key679 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key680 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key681 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key682 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.unit, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key683 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key684 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key685 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key686 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key687 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key688 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key689 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key690 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key691 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key692 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key693 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key694 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key695 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key696 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key697 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key698 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key699 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key700 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key701 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key702 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key703 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key704 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key705 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key706 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key707 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key708 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key709 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.hyperplane, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key710 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key711 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key712 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key713 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key714 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key715 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key716 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key717 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key718 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key719 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.exceptional 0, 1⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key720 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.point, 0⟩,
      ⟨.point, 0⟩,
      ⟨.point, 0⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key721 : SurfaceAncestorKey .hirzebruchOne :=
  ⟨1, ![1, 1],
    ([
      ⟨.point, 0⟩,
      ⟨.point, 1⟩
    ] : List (SurfaceInsertion .hirzebruchOne)), by decide⟩

def key (i : Fin 722) : SurfaceAncestorKey .hirzebruchOne :=
  (#[
    key000, key001, key002, key003, key004, key005, key006, key007,
    key008, key009, key010, key011, key012, key013, key014, key015,
    key016, key017, key018, key019, key020, key021, key022, key023,
    key024, key025, key026, key027, key028, key029, key030, key031,
    key032, key033, key034, key035, key036, key037, key038, key039,
    key040, key041, key042, key043, key044, key045, key046, key047,
    key048, key049, key050, key051, key052, key053, key054, key055,
    key056, key057, key058, key059, key060, key061, key062, key063,
    key064, key065, key066, key067, key068, key069, key070, key071,
    key072, key073, key074, key075, key076, key077, key078, key079,
    key080, key081, key082, key083, key084, key085, key086, key087,
    key088, key089, key090, key091, key092, key093, key094, key095,
    key096, key097, key098, key099, key100, key101, key102, key103,
    key104, key105, key106, key107, key108, key109, key110, key111,
    key112, key113, key114, key115, key116, key117, key118, key119,
    key120, key121, key122, key123, key124, key125, key126, key127,
    key128, key129, key130, key131, key132, key133, key134, key135,
    key136, key137, key138, key139, key140, key141, key142, key143,
    key144, key145, key146, key147, key148, key149, key150, key151,
    key152, key153, key154, key155, key156, key157, key158, key159,
    key160, key161, key162, key163, key164, key165, key166, key167,
    key168, key169, key170, key171, key172, key173, key174, key175,
    key176, key177, key178, key179, key180, key181, key182, key183,
    key184, key185, key186, key187, key188, key189, key190, key191,
    key192, key193, key194, key195, key196, key197, key198, key199,
    key200, key201, key202, key203, key204, key205, key206, key207,
    key208, key209, key210, key211, key212, key213, key214, key215,
    key216, key217, key218, key219, key220, key221, key222, key223,
    key224, key225, key226, key227, key228, key229, key230, key231,
    key232, key233, key234, key235, key236, key237, key238, key239,
    key240, key241, key242, key243, key244, key245, key246, key247,
    key248, key249, key250, key251, key252, key253, key254, key255,
    key256, key257, key258, key259, key260, key261, key262, key263,
    key264, key265, key266, key267, key268, key269, key270, key271,
    key272, key273, key274, key275, key276, key277, key278, key279,
    key280, key281, key282, key283, key284, key285, key286, key287,
    key288, key289, key290, key291, key292, key293, key294, key295,
    key296, key297, key298, key299, key300, key301, key302, key303,
    key304, key305, key306, key307, key308, key309, key310, key311,
    key312, key313, key314, key315, key316, key317, key318, key319,
    key320, key321, key322, key323, key324, key325, key326, key327,
    key328, key329, key330, key331, key332, key333, key334, key335,
    key336, key337, key338, key339, key340, key341, key342, key343,
    key344, key345, key346, key347, key348, key349, key350, key351,
    key352, key353, key354, key355, key356, key357, key358, key359,
    key360, key361, key362, key363, key364, key365, key366, key367,
    key368, key369, key370, key371, key372, key373, key374, key375,
    key376, key377, key378, key379, key380, key381, key382, key383,
    key384, key385, key386, key387, key388, key389, key390, key391,
    key392, key393, key394, key395, key396, key397, key398, key399,
    key400, key401, key402, key403, key404, key405, key406, key407,
    key408, key409, key410, key411, key412, key413, key414, key415,
    key416, key417, key418, key419, key420, key421, key422, key423,
    key424, key425, key426, key427, key428, key429, key430, key431,
    key432, key433, key434, key435, key436, key437, key438, key439,
    key440, key441, key442, key443, key444, key445, key446, key447,
    key448, key449, key450, key451, key452, key453, key454, key455,
    key456, key457, key458, key459, key460, key461, key462, key463,
    key464, key465, key466, key467, key468, key469, key470, key471,
    key472, key473, key474, key475, key476, key477, key478, key479,
    key480, key481, key482, key483, key484, key485, key486, key487,
    key488, key489, key490, key491, key492, key493, key494, key495,
    key496, key497, key498, key499, key500, key501, key502, key503,
    key504, key505, key506, key507, key508, key509, key510, key511,
    key512, key513, key514, key515, key516, key517, key518, key519,
    key520, key521, key522, key523, key524, key525, key526, key527,
    key528, key529, key530, key531, key532, key533, key534, key535,
    key536, key537, key538, key539, key540, key541, key542, key543,
    key544, key545, key546, key547, key548, key549, key550, key551,
    key552, key553, key554, key555, key556, key557, key558, key559,
    key560, key561, key562, key563, key564, key565, key566, key567,
    key568, key569, key570, key571, key572, key573, key574, key575,
    key576, key577, key578, key579, key580, key581, key582, key583,
    key584, key585, key586, key587, key588, key589, key590, key591,
    key592, key593, key594, key595, key596, key597, key598, key599,
    key600, key601, key602, key603, key604, key605, key606, key607,
    key608, key609, key610, key611, key612, key613, key614, key615,
    key616, key617, key618, key619, key620, key621, key622, key623,
    key624, key625, key626, key627, key628, key629, key630, key631,
    key632, key633, key634, key635, key636, key637, key638, key639,
    key640, key641, key642, key643, key644, key645, key646, key647,
    key648, key649, key650, key651, key652, key653, key654, key655,
    key656, key657, key658, key659, key660, key661, key662, key663,
    key664, key665, key666, key667, key668, key669, key670, key671,
    key672, key673, key674, key675, key676, key677, key678, key679,
    key680, key681, key682, key683, key684, key685, key686, key687,
    key688, key689, key690, key691, key692, key693, key694, key695,
    key696, key697, key698, key699, key700, key701, key702, key703,
    key704, key705, key706, key707, key708, key709, key710, key711,
    key712, key713, key714, key715, key716, key717, key718, key719,
    key720, key721
  ] : Array (SurfaceAncestorKey .hirzebruchOne))[i.val]

def value (i : Fin 722) : ℚ :=
  (#[
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
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
    (0 / 1 : ℚ),
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
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (2 / 1 : ℚ),
    (2 / 1 : ℚ),
    (2 / 1 : ℚ),
    (2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-3 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-4 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-3 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-4 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-3 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-2 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 1 : ℚ),
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
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (-1 / 1 : ℚ),
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
    (1 / 1 : ℚ),
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
    (1 / 1 : ℚ),
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
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (2 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (1 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
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
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 1 : ℚ),
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
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (1 / 6 : ℚ),
    (-1 / 8 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 24 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 8 : ℚ),
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
    (-1 / 24 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
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
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (1 / 24 : ℚ),
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
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (-1 / 12 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
    (0 / 1 : ℚ),
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
    (-1 / 12 : ℚ)
  ] : Array ℚ)[i.val]

def entries (i : Fin 722) : RationalTerms (SurfaceAncestorKey .hirzebruchOne) :=
  RationalTerms.term (value i) 0

end AxiomaticGW.BlowupF1CompleteHComponents
