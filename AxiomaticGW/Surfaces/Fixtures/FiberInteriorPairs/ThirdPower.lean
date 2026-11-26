/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.SecondPower

/-! # F₁ fiber component certificates at total cotangent power 3
Each entry replays the original rational or elliptic boundary equation on the
preceding degree layers. The table lookup checks the entire ancestor key.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs.Components.ThirdPower
open SurfaceGenusTwoPositiveSquare
set_option Elab.async false
set_option maxRecDepth 65536

abbrev previous := SecondPower.components

def bucket0 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, H 1, E 2]) (1 / 3),
   previous.entry (node 1 fiberClass [H 0, H 0, unit 1, H 2]) (-1 / 8)]

def bucket1 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [E 0, E 1, unit 2]) (1 / 3),
   previous.entry (node 1 fiberClass [pt 0, unit 1, unit 1, E 1]) (-1 / 2)]

def bucket4 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, unit 0, pt 1, H 2]) (-1 / 4)]

def bucket5 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [E 0, unit 1, H 2]) (1 / 3)]

def bucket9 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [E 0, E 0, unit 1, E 2]) (5 / 8)]

def bucket10 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [E 0, unit 1, H 1, E 1]) (1 / 4)]

def bucket11 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, H 0, H 1, E 2]) (-1 / 24),
   previous.entry (node 1 fiberClass [unit 0, unit 1, E 1, pt 1]) (-1 / 2)]

def bucket13 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, unit 1, E 2]) (1 / 3)]

def bucket14 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, E 1, E 2]) (1 / 3),
   previous.entry (node 1 fiberClass [E 0, E 0, H 1, unit 2]) (3 / 8)]

def bucket16 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 1, H 1, H 1]) (1 / 3)]

def bucket17 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, E 0, E 1, H 2]) (5 / 24)]

def bucket18 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, pt 0, unit 1, E 2]) (-1 / 4),
   previous.entry (node 1 fiberClass [H 0, H 1, unit 2]) (1 / 3)]

def bucket23 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, pt 0, H 1, unit 2]) (-1 / 4),
   previous.entry (node 1 fiberClass [unit 0, H 1, H 2]) (1 / 3)]

def bucket24 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, H 0, unit 1, E 2]) (1 / 8),
   previous.entry (node 1 fiberClass [E 0, unit 1, E 1, E 1]) (3 / 4)]

def bucket27 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, unit 1, H 1, H 1]) (-3 / 4)]

def bucket28 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, unit 0, pt 1, E 2]) (-1 / 4),
   previous.entry (node 1 fiberClass [E 0, E 0, E 1, unit 2]) (5 / 8)]

def bucket29 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, H 0, H 1, unit 2]) (-1 / 8),
   previous.entry (node 1 fiberClass [E 0, unit 1, E 2]) (1 / 3)]

def bucket30 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 1, H 1, E 1]) (1 / 3)]

def bucket32 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, E 1, unit 2]) (1 / 3),
   previous.entry (node 1 fiberClass [E 0, E 0, unit 1, H 2]) (3 / 8)]

def bucket34 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, H 0, H 1, H 2]) (-7 / 24),
   previous.entry (node 1 fiberClass [E 0, H 1, unit 2]) (1 / 3),
   previous.entry (node 1 fiberClass [pt 0, unit 1, unit 1, H 1]) (-1 / 2)]

def bucket36 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, unit 1, H 2]) (1 / 3)]

def bucket37 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, pt 0, E 1, unit 2]) (-1 / 4),
   previous.entry (node 1 fiberClass [unit 0, E 1, H 2]) (1 / 3)]

def bucket41 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, E 0, E 1, E 2]) (11 / 24),
   previous.entry (node 1 fiberClass [unit 0, pt 0, unit 1, H 2]) (-1 / 4),
   previous.entry (node 1 fiberClass [H 0, unit 1, H 1, E 1]) (-1 / 4)]

def bucket43 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, H 0, E 1, unit 2]) (1 / 8)]

def bucket44 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, unit 1, H 1, pt 1]) (-1 / 2),
   previous.entry (node 1 fiberClass [unit 1, E 1, E 1]) (1 / 3)]

def candidates : ℕ → List (Entry X)
  | 0 => bucket0
  | 1 => bucket1
  | 4 => bucket4
  | 5 => bucket5
  | 9 => bucket9
  | 10 => bucket10
  | 11 => bucket11
  | 13 => bucket13
  | 14 => bucket14
  | 16 => bucket16
  | 17 => bucket17
  | 18 => bucket18
  | 23 => bucket23
  | 24 => bucket24
  | 27 => bucket27
  | 28 => bucket28
  | 29 => bucket29
  | 30 => bucket30
  | 32 => bucket32
  | 34 => bucket34
  | 36 => bucket36
  | 37 => bucket37
  | 41 => bucket41
  | 43 => bucket43
  | 44 => bucket44
  | _ => []

/-- Extend the certified evaluator with the stored degree-3 vertices. -/
def components : CertifiedComponents X := previous.layer 3 candidates

end AxiomaticGW.BlowupF1FiberInteriorPairs.Components.ThirdPower
