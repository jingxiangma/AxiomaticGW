/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoSecondUnitCache

/-! # Certified lower-genus components of total cotangent power at least two

The finite bucket index is used only for screening. Each match checks the
whole stable ancestor key, and every stored rational is kernel evaluated.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.OneBlowupCache
open SurfaceGenusTwoPositiveSquare
set_option Elab.async false
set_option maxRecDepth 65536

def bucket0 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 12), by decide +kernel⟩]

def bucket3 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket4 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 3), by decide +kernel⟩]

def bucket5 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 24), by decide +kernel⟩]

def bucket7 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket8 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 4), by decide +kernel⟩]

def bucket9 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 6), by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket10 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
       ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    2, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket12 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-7 / 24), by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket13 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 1⟩, ⟨.point, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 6), by decide +kernel⟩]

def bucket14 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩,
       ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket16 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket17 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket18 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 4), by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket19 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩,
       ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket20 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 8), by decide +kernel⟩]

def bucket23 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket25 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
       ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket26 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket27 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 1⟩, ⟨.point, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-3 / 8), by decide +kernel⟩]

def bucket28 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 6), by decide +kernel⟩]

def bucket29 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
       ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket30 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩,
       ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    -1, by decide +kernel⟩]

def bucket31 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.unit, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket32 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 12), by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 12), by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 8), by decide +kernel⟩]

def bucket34 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩,
       ⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket36 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (-1 / 24), by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.unit, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket38 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![0, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket39 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket40 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
       ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    (1 / 6), by decide +kernel⟩]

def bucket41 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.point, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.exceptional 0, 0⟩, ⟨.exceptional 0, 0⟩, ⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket42 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩, ⟨.unit, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket43 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket45 : List (Entry .hirzebruchOne) :=
  [⟨⟨0, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 0⟩, ⟨.hyperplane, 0⟩,
       ⟨.exceptional 0, 0⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.hyperplane, 0⟩, ⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

def bucket46 : List (Entry .hirzebruchOne) :=
  [⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.unit, 0⟩, ⟨.point, 1⟩, ⟨.unit, 2⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩,
   ⟨⟨1, ![1, 0],
      ([⟨.unit, 0⟩, ⟨.hyperplane, 1⟩, ⟨.exceptional 0, 1⟩] :
        List (SurfaceInsertion .hirzebruchOne)), by decide⟩,
    0, by decide +kernel⟩]

/-- Return the previously checked candidates for this index. -/
def pool : ℕ → List (Entry .hirzebruchOne)
  | 0 => bucket0
  | 3 => bucket3
  | 4 => bucket4
  | 5 => bucket5
  | 7 => bucket7
  | 8 => bucket8
  | 9 => bucket9
  | 10 => bucket10
  | 12 => bucket12
  | 13 => bucket13
  | 14 => bucket14
  | 16 => bucket16
  | 17 => bucket17
  | 18 => bucket18
  | 19 => bucket19
  | 20 => bucket20
  | 23 => bucket23
  | 25 => bucket25
  | 26 => bucket26
  | 27 => bucket27
  | 28 => bucket28
  | 29 => bucket29
  | 30 => bucket30
  | 31 => bucket31
  | 32 => bucket32
  | 34 => bucket34
  | 36 => bucket36
  | 38 => bucket38
  | 39 => bucket39
  | 40 => bucket40
  | 41 => bucket41
  | 42 => bucket42
  | 43 => bucket43
  | 45 => bucket45
  | 46 => bucket46
  | _ => []

end AxiomaticGW.GenusTwoSecondUnitPairs.OneBlowupCache
