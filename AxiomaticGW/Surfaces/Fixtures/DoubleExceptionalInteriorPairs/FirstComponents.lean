/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.FirstPower
public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.OneBlowupCache

/-! # Certified lower-genus components of total cotangent power 1 for the class 2E on F₁

Each stored value is checked against the original cotangent boundary on its complete key.
The stage also accepts previously certified components at class zero and at E.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs.Components.FirstComponents
open SurfaceGenusTwoPositiveSquare
open BlowupF1FiberInteriorPairs.Components (X node zeroClass unit H E pt)

set_option Elab.async false
set_option maxRecDepth 65536

abbrev exceptional : X.Curve := ![1, 0]
abbrev doubleExceptional : X.Curve := ![2, 0]

abbrev previous := CertifiedComponents.bounded X

def bucket0 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, E 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, pt 1]) 0]

def bucket1 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, H 0, pt 1]) 0]

def bucket2 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 exceptional [unit 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, pt 0, E 1]) 0]

def bucket3 : List (Entry X) :=
  [previous.entry (node 0 exceptional [H 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, E 1]) 0]

def bucket4 : List (Entry X) :=
  [previous.entry (node 0 zeroClass [pt 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, unit 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, E 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, pt 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 0, pt 1]) 0]

def bucket5 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, pt 0, pt 1]) 0]

def bucket6 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, E 0, E 0, unit 1]) (-3),
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 1 exceptional [H 0, unit 1]) 0,
   previous.entry (node 1 exceptional [E 1]) (1 / 24),
   previous.entry (node 1 doubleExceptional [pt 0, pt 0, E 1]) 0]

def bucket7 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 exceptional [pt 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, E 0, E 1]) 3,
   previous.entry (node 1 doubleExceptional [E 0, pt 0, unit 1]) 0]

def bucket8 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 exceptional [unit 0, pt 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [unit 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 0, E 0, E 1]) 0]

def bucket9 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, unit 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, unit 1]) 0]

def bucket10 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, H 1]) 0]

def bucket11 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, E 0, E 0, E 0, E 1]) 1,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 exceptional [unit 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [unit 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, unit 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, H 0, pt 1]) 0]

def bucket12 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, unit 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, pt 0, pt 1]) 0]

def bucket13 : List (Entry X) :=
  [previous.entry (node 0 zeroClass [H 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 0, E 1]) (1 / 12),
   previous.entry (node 1 doubleExceptional [unit 0, unit 1]) 0]

def bucket14 : List (Entry X) :=
  [previous.entry (node 0 exceptional [H 0, H 0, E 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 0, H 1]) 0,
   previous.entry (node 1 exceptional [E 0, pt 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, E 0, E 1]) 0]

def bucket15 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, pt 0, pt 1]) 0]

def bucket16 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, E 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, pt 1]) 0]

def bucket17 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, E 0, pt 1]) 0]

def bucket18 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, pt 0, E 1]) 0]

def bucket19 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 exceptional [E 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, pt 0, unit 1]) 0,
   previous.entry (node 1 exceptional [unit 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [E 0, H 1]) 0]

def bucket20 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 1 exceptional [unit 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, H 1]) 0]

def bucket21 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 exceptional [pt 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, H 0, H 1]) 0]

def bucket22 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, H 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, pt 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 exceptional [unit 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [E 0, unit 1]) 0]

def bucket23 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, unit 1]) 0]

def bucket24 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, E 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 0, H 1]) 0]

def bucket25 : List (Entry X) :=
  [previous.entry (node 0 exceptional [H 0, H 0, H 0, E 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, pt 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [pt 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, unit 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, pt 0, H 1]) 0]

def bucket26 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, E 0, unit 1]) 2,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [unit 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 0, pt 1]) 0]

def bucket27 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, unit 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, E 1]) (-1),
   previous.entry (node 1 exceptional [unit 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, E 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 0, unit 1]) 0]

def bucket28 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, pt 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, pt 0, unit 1]) 0]

def bucket29 : List (Entry X) :=
  [previous.entry (node 0 zeroClass [E 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, pt 0, pt 1]) 0]

def bucket30 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, E 0, E 1]) 0]

def bucket31 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, E 1]) (-1),
   previous.entry (node 0 exceptional [E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, H 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, pt 0, pt 1]) 0]

def bucket32 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 0, pt 0, unit 1]) 0]

def bucket33 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 1]) (-1 / 12)]

def bucket34 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, E 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, E 0, E 0, E 1]) (-7),
   previous.entry (node 1 doubleExceptional [H 0, E 1]) 0]

def bucket35 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, E 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 1 exceptional [unit 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, H 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, pt 0, H 1]) 0]

def bucket36 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, H 0, E 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 1 exceptional [unit 0, unit 0, pt 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 1]) 0]

def bucket37 : List (Entry X) :=
  [previous.entry (node 0 zeroClass [pt 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, unit 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, H 0, E 1]) 0,
   previous.entry (node 1 exceptional [E 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, E 0, H 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, pt 1]) 0]

def bucket38 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, E 0, E 0, E 1]) (-1),
   previous.entry (node 0 exceptional [H 0, H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, E 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, E 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, unit 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, pt 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 0, E 1]) 0]

def bucket39 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, pt 0, pt 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, pt 0, pt 0, unit 1]) 0,
   previous.entry (node 1 exceptional [H 1]) 0,
   previous.entry (node 1 doubleExceptional [unit 0, pt 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 0, pt 0, H 1]) 0]

def bucket40 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, pt 0, E 1]) 0,
   previous.entry (node 0 exceptional [unit 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 0, E 0, E 1]) (-1 / 12)]

def bucket41 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, unit 0, pt 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, E 0, E 0, unit 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 0, E 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, H 0, pt 1]) 0]

def bucket42 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, E 0, E 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [H 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, H 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [E 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 1 doubleExceptional [pt 0, pt 0, unit 1]) 0]

def bucket43 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, H 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, H 0, E 0, pt 0, pt 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, E 0, E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 1 exceptional [unit 0, unit 1]) 0,
   previous.entry (node 1 doubleExceptional [E 0, E 0, pt 1]) 0]

def bucket44 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, E 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 exceptional [unit 0, E 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, unit 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, E 0, pt 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 1 exceptional [H 0, E 0, E 1]) 0]

def bucket45 : List (Entry X) :=
  [previous.entry (node 0 exceptional [H 0, H 0, H 0, unit 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, H 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, E 0, H 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 1 exceptional [H 0, pt 0, pt 1]) 0,
   previous.entry (node 1 doubleExceptional [H 0, H 0, E 1]) 0]

def bucket46 : List (Entry X) :=
  [previous.entry (node 0 exceptional [unit 0, H 0, H 0, E 1]) 0,
   previous.entry (node 0 exceptional [H 0, H 0, pt 0, H 1]) 0,
   previous.entry (node 0 exceptional [E 0, E 0, E 0, unit 1]) (-1),
   previous.entry (node 0 exceptional [E 0, pt 0, pt 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, H 0, E 0, pt 1]) 0,
   previous.entry (node 0 doubleExceptional [unit 0, unit 0, pt 0, unit 1]) 0,
   previous.entry (node 0 doubleExceptional [H 0, E 0, pt 0, E 1]) 0,
   previous.entry (node 1 exceptional [E 0, E 0, H 1]) 0]

def newEntries : ℕ → List (Entry X)
  | 0 => bucket0
  | 1 => bucket1
  | 2 => bucket2
  | 3 => bucket3
  | 4 => bucket4
  | 5 => bucket5
  | 6 => bucket6
  | 7 => bucket7
  | 8 => bucket8
  | 9 => bucket9
  | 10 => bucket10
  | 11 => bucket11
  | 12 => bucket12
  | 13 => bucket13
  | 14 => bucket14
  | 15 => bucket15
  | 16 => bucket16
  | 17 => bucket17
  | 18 => bucket18
  | 19 => bucket19
  | 20 => bucket20
  | 21 => bucket21
  | 22 => bucket22
  | 23 => bucket23
  | 24 => bucket24
  | 25 => bucket25
  | 26 => bucket26
  | 27 => bucket27
  | 28 => bucket28
  | 29 => bucket29
  | 30 => bucket30
  | 31 => bucket31
  | 32 => bucket32
  | 33 => bucket33
  | 34 => bucket34
  | 35 => bucket35
  | 36 => bucket36
  | 37 => bucket37
  | 38 => bucket38
  | 39 => bucket39
  | 40 => bucket40
  | 41 => bucket41
  | 42 => bucket42
  | 43 => bucket43
  | 44 => bucket44
  | 45 => bucket45
  | 46 => bucket46
  | _ => []

/-- Extend the certified total evaluator with these full-key lower-genus values. -/
def components : CertifiedComponents X := previous.layer 1 fun i ↦
  newEntries i ++ BlowupF1FiberInteriorPairs.Components.FirstPower.candidates i

end AxiomaticGW.BlowupF1DoubleExceptionalInteriorPairs.Components.FirstComponents
