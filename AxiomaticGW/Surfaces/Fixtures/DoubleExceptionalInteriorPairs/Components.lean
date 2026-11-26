/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.DoubleExceptionalInteriorPairs.ThirdComponents

/-! # Certified lower-genus components of total cotangent power 4 for the class 2E on F₁

Each stored value is checked against the original cotangent boundary on its complete key.
The stage also accepts previously certified components at class zero and at E.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs.Components
open SurfaceGenusTwoPositiveSquare
open BlowupF1FiberInteriorPairs.Components (X node zeroClass unit H E pt)

set_option Elab.async false
set_option maxRecDepth 65536

abbrev exceptional : X.Curve := ![1, 0]
abbrev doubleExceptional : X.Curve := ![2, 0]

abbrev previous :=
  AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs.Components.ThirdComponents.components

def bucket3 : List (Entry X) :=
  [previous.entry (node 1 doubleExceptional [H 0, H 0, unit 1, unit 3]) 0]

def bucket7 : List (Entry X) :=
  [previous.entry (node 1 doubleExceptional [unit 0, unit 0, pt 1, unit 3]) 0]

def bucket20 : List (Entry X) :=
  [previous.entry (node 1 doubleExceptional [unit 0, E 0, E 1, unit 3]) (1 / 8)]

def bucket35 : List (Entry X) :=
  [previous.entry (node 1 doubleExceptional [E 0, E 0, unit 1, unit 3]) (1 / 8)]

def bucket37 : List (Entry X) :=
  [previous.entry (node 1 doubleExceptional [unit 0, H 0, H 1, unit 3]) 0]

def bucket44 : List (Entry X) :=
  [previous.entry (node 1 doubleExceptional [unit 0, pt 0, unit 1, unit 3]) 0]

def newEntries : ℕ → List (Entry X)
  | 3 => bucket3
  | 7 => bucket7
  | 20 => bucket20
  | 35 => bucket35
  | 37 => bucket37
  | 44 => bucket44
  | _ => []

/-- Extend the certified total evaluator with these full-key lower-genus values. -/
def components : CertifiedComponents X := previous.layer 4 fun i ↦
  newEntries i ++ GenusTwoSecondUnitPairs.OneBlowupCache.pool i

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs.Components
