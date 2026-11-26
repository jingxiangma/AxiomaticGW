/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.ThirdPower

/-! # F₁ fiber component certificates at total cotangent power 4
Each entry replays the original rational or elliptic boundary equation on the
preceding degree layers. The table lookup checks the entire ancestor key.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs.Components.FourthPower
open SurfaceGenusTwoPositiveSquare
set_option Elab.async false
set_option maxRecDepth 65536

abbrev previous := ThirdPower.components

def bucket8 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [E 0, E 0, unit 1, unit 3]) (1 / 2)]

def bucket10 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, H 0, H 1, unit 3]) (1 / 2)]

def bucket12 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, unit 1, unit 3]) 0]

def bucket13 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, E 1, unit 3]) 0]

def bucket17 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, pt 0, unit 1, unit 3]) 0]

def bucket23 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [H 0, H 0, unit 1, unit 3]) (1 / 2)]

def bucket27 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, unit 0, pt 1, unit 3]) 0]

def bucket28 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [E 0, unit 1, unit 3]) 0]

def bucket40 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, E 0, E 1, unit 3]) (1 / 2)]

def bucket46 : List (Entry X) :=
  [previous.entry (node 1 fiberClass [unit 0, H 1, unit 3]) 0]

def candidates : ℕ → List (Entry X)
  | 8 => bucket8
  | 10 => bucket10
  | 12 => bucket12
  | 13 => bucket13
  | 17 => bucket17
  | 23 => bucket23
  | 27 => bucket27
  | 28 => bucket28
  | 40 => bucket40
  | 46 => bucket46
  | _ => []

/-- Extend the certified evaluator with the stored degree-4 vertices. -/
def components : CertifiedComponents X := previous.layer 4 candidates

end AxiomaticGW.BlowupF1FiberInteriorPairs.Components.FourthPower
