/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowupComponents

/-! # Frequently reused one-power vertices for the two-point blowup
Each stored lower-genus result is checked on its full class and insertions.
Omitted keys fall back to the dimension-pruned coordinate recursion.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupFirstPower
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache TwoBlowupComponents
set_option Elab.async false
set_option maxRecDepth 65536

def bucket0 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, a₀, a₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, a₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, h₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [b₀, b₀, b₀, u₁]) (-1),
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 z [u₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 z [h₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, a₀, b₁]) 0]

def bucket1 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, p₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, h₀, a₁]) 0,
   boundedEntry (componentKey 1 z [h₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [b₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, b₀, a₁]) 0]

def bucket2 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, a₀, a₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [a₀, h₁]) 0,
   lineEntry (componentKey 1 l [h₀, h₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 l [h₀, p₀, a₁]) 0,
   lineEntry (componentKey 1 e₁ [u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 1 e₁ [b₀, b₀, b₁]) 0]

def bucket3 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, u₁]) (-1),
   boundedEntry (componentKey 0 z [u₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 z [u₀, b₁]) (-1 / 24),
   boundedEntry (componentKey 1 z [p₀, p₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, a₀, a₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, h₁]) 0]

def bucket4 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, h₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 l [u₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, b₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 z [u₀, u₀, b₁]) 0,
   boundedEntry (componentKey 1 z [b₀, a₁]) 0,
   boundedEntry (componentKey 1 l [a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 l [p₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, h₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, h₀, h₁]) 0]

def bucket5 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [h₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, b₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, b₀, p₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, b₀, a₁]) 0,
   boundedEntry (componentKey 1 z [u₀, p₁]) 0,
   boundedEntry (componentKey 1 z [b₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 l [u₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 l [h₀, a₀, a₁]) (-1 / 12)]

def bucket6 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, b₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, h₀, u₁]) 1,
   boundedEntry (componentKey 0 l [h₀, a₀, a₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, p₀, u₁]) 0,
   lineEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, u₀, p₁]) 0,
   boundedEntry (componentKey 1 z [a₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 l [h₀, b₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 l [b₀, p₀, a₁]) 0]

def bucket7 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, a₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [a₀, a₀, a₀, u₁]) 1,
   boundedEntry (componentKey 0 l [a₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 l [u₀, p₀, p₁]) 0,
   lineEntry (componentKey 1 l [a₀, a₀, h₁]) (-1 / 12),
   lineEntry (componentKey 1 l [a₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [h₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [b₀, h₁]) 0]

def bucket8 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [b₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, b₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 l [u₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, h₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, u₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, b₀, h₁]) 0]

def bucket9 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 1 z [a₀, a₀, b₁]) 0,
   lineEntry (componentKey 1 l [a₀, b₀, a₁]) (-1 / 12)]

def bucket10 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, b₀, u₁]) 1,
   boundedEntry (componentKey 0 l [a₀, a₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, h₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, p₀, h₁]) 0,
   lineEntry (componentKey 1 l [u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 1 l [b₀, b₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [a₀, p₀, a₁]) 0]

def bucket11 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 e₁ [u₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, h₀, a₁]) 0,
   lineEntry (componentKey 1 l [h₀, h₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, u₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [b₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [b₀, p₀, b₁]) 0]

def bucket12 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, b₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, b₀, b₀, h₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 l [u₀, h₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, b₀, a₁]) 0]

def bucket13 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 z [h₀, b₁]) 0,
   boundedEntry (componentKey 1 z [p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, u₀, p₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, a₀, a₁]) (1 / 12)]

def bucket14 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, p₀, u₁]) 0,
   lineEntry (componentKey 0 l [u₀, h₀, h₀, a₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 l [h₀, b₀, b₀, u₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, a₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, h₀, b₁]) 0,
   boundedEntry (componentKey 1 z [u₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 z [b₀, p₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, h₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, b₀, b₁]) 0]

def bucket15 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, b₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [b₀, b₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, b₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 1 z [h₀, b₀, a₁]) 0,
   boundedEntry (componentKey 1 z [h₀, p₁]) 0,
   boundedEntry (componentKey 1 l [u₀, a₁]) 0,
   boundedEntry (componentKey 1 l [h₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 l [b₀, h₁]) (-1 / 12)]

def bucket16 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, a₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 1 z [a₀, a₁]) 0,
   boundedEntry (componentKey 1 l [u₀, u₀, a₁]) 0,
   boundedEntry (componentKey 1 l [u₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, a₀, b₁]) 0]

def bucket17 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, a₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [b₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, h₀, h₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, b₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, a₀, a₁]) 0,
   boundedEntry (componentKey 1 z [a₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 z [b₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, p₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [u₀, p₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, a₁]) 0]

def bucket18 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, u₁]) 1,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, b₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, h₀, a₁]) 1,
   boundedEntry (componentKey 0 l [h₀, a₀, a₀, a₀, u₁]) 2,
   boundedEntry (componentKey 0 l [b₀, b₀, b₀, u₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, b₀, b₁]) 0,
   lineEntry (componentKey 1 l [h₀, a₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 l [a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, h₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, h₀, a₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, b₀, h₁]) 0]

def bucket19 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, h₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 l [u₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [a₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, b₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 1 z [b₀, p₁]) 0,
   boundedEntry (componentKey 1 l [b₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, h₁]) 0]

def bucket20 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [a₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, a₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, b₁]) 0]

def bucket21 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, p₀, u₁]) 1,
   boundedEntry (componentKey 0 z [u₀, p₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, h₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, b₀, b₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 l [a₀, a₀, a₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, h₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, u₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [b₀, a₁]) 0]

def bucket22 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, u₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, b₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, a₀, u₁]) 1,
   boundedEntry (componentKey 0 l [a₀, a₀, a₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, a₀, p₀, b₁]) 0,
   lineEntry (componentKey 0 e₁ [u₀, h₀, a₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, b₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 l [h₀, h₀, h₁]) (-1 / 12),
   lineEntry (componentKey 1 l [a₀, b₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [h₀, b₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, b₀, a₁]) 0,
   lineEntry (componentKey 1 e₁ [b₀, b₀, h₁]) 0]

def bucket23 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, b₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, a₀, p₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, h₁]) (-1 / 8),
   boundedEntry (componentKey 1 z [p₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, u₀, p₁]) 0,
   boundedEntry (componentKey 1 e₁ [a₀, p₀, b₁]) 0]

def bucket24 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, p₁]) 1,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [b₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, h₀, p₀, a₁]) 0,
   lineEntry (componentKey 0 e₁ [u₀, a₀, a₀, a₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 z [u₀, u₀, h₁]) 0,
   boundedEntry (componentKey 1 z [h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 1 z [h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, a₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [b₀, b₁]) (-1 / 12)]

def bucket25 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, u₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, b₀, b₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [b₀, b₀, b₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 l [u₀, p₀, h₁]) 0,
   lineEntry (componentKey 1 l [h₀, a₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, b₀, b₁]) 0]

def bucket26 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, b₀, b₀, u₁]) (-1),
   boundedEntry (componentKey 0 z [a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [b₀, b₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, b₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [h₀, a₀, b₀, u₁]) 1,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, a₀, a₀, u₁]) 2,
   boundedEntry (componentKey 1 z [a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 z [p₀, b₁]) 0,
   boundedEntry (componentKey 1 l [u₀, h₀, a₁]) 0,
   lineEntry (componentKey 1 l [h₀, b₀, h₁]) (-1 / 12),
   lineEntry (componentKey 1 e₁ [a₀, a₀, b₁]) 0]

def bucket27 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, b₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, a₀, a₀, b₁]) 1,
   boundedEntry (componentKey 0 l [b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 z [u₀, p₀, b₁]) 0,
   boundedEntry (componentKey 1 z [h₀, a₀, a₁]) 0,
   lineEntry (componentKey 1 l [a₀, h₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 1 e₁ [h₀, p₀, h₁]) 0]

def bucket28 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 z [b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 z [p₀, p₁]) 0,
   boundedEntry (componentKey 1 l [u₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 l [u₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, h₀, a₁]) 0]

def bucket29 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [h₀, b₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, b₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 1 z [a₀, a₀, h₁]) 0,
   boundedEntry (componentKey 1 z [a₀, b₁]) 0,
   boundedEntry (componentKey 1 l [u₀, u₀, b₁]) 0,
   lineEntry (componentKey 1 l [b₀, a₁]) (-1 / 12)]

def bucket30 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, h₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, a₀, p₀, b₁]) 0,
   lineEntry (componentKey 0 l [u₀, h₀, a₀, a₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 l [h₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [a₀, b₀, b₀, u₁]) 1,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, b₀, b₀, p₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 l [u₀, b₀, a₁]) 0,
   lineEntry (componentKey 1 l [b₀, b₀, h₁]) (-1 / 12),
   lineEntry (componentKey 1 e₁ [h₀, a₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [p₀, a₁]) 0]

def bucket31 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, h₀, b₁]) 1,
   boundedEntry (componentKey 0 l [u₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [a₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 z [a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 1 z [a₀, p₁]) 0,
   boundedEntry (componentKey 1 l [u₀, u₀, p₁]) 0,
   boundedEntry (componentKey 1 l [a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, h₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [u₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [b₀, p₀, h₁]) 0]

def bucket32 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, h₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, h₀, p₀, a₁]) 0,
   lineEntry (componentKey 0 l [u₀, a₀, a₀, a₀, a₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, a₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 1 z [b₀, b₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, b₀, a₁]) 0]

def bucket33 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, h₀, a₀, u₁]) 2,
   boundedEntry (componentKey 0 l [b₀, b₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, h₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [p₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [u₀, h₀, p₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, a₁]) (-1 / 12)]

def bucket34 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, a₀, a₁]) 1,
   boundedEntry (componentKey 0 l [h₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [a₀, a₀, a₀, a₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, b₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [b₀, b₀, b₀, p₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, h₀, h₁]) 0,
   lineEntry (componentKey 1 l [a₀, a₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, p₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, a₀, a₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, b₀, h₁]) 0,
   boundedEntry (componentKey 1 e₁ [b₀, b₁]) 0]

def bucket35 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, a₀, a₁]) (-1),
   boundedEntry (componentKey 0 z [u₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, b₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, b₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 l [h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 e₂ [b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, b₀, b₁]) 0]

def bucket36 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, b₀, b₁]) (-1),
   boundedEntry (componentKey 0 z [h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, a₀, h₁]) 1,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, b₀, b₀, p₀, u₁]) 0,
   lineEntry (componentKey 1 l [h₀, h₀, a₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, p₀, p₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [b₀, b₀, a₁]) 0]

def bucket37 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, b₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [u₀, b₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, a₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, a₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, b₀, b₀, b₀, u₁]) 0,
   lineEntry (componentKey 1 z [u₀, a₁]) (-1 / 24),
   boundedEntry (componentKey 1 z [h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 1 z [b₀, h₁]) 0,
   boundedEntry (componentKey 1 z [p₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, b₀, p₁]) 0]

def bucket38 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [h₀, a₀, a₀, u₁]) 1,
   boundedEntry (componentKey 0 l [h₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [u₀, u₀, a₁]) 0,
   lineEntry (componentKey 1 z [u₀, b₀, h₁]) 0,
   lineEntry (componentKey 1 l [h₀, a₀, h₁]) (-1 / 12),
   lineEntry (componentKey 1 l [h₀, b₁]) (-1 / 12),
   boundedEntry (componentKey 1 l [p₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [a₀, b₀, a₁]) 0]

def bucket39 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, a₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, b₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [a₀, a₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, a₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 l [u₀, h₀, b₁]) 0,
   lineEntry (componentKey 1 l [u₀, p₀, a₁]) 0,
   boundedEntry (componentKey 1 l [b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, a₀, p₁]) 0,
   boundedEntry (componentKey 1 e₂ [b₀, b₀, b₁]) (1 / 12)]

def bucket40 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, h₀, h₀, a₁]) 0,
   boundedEntry (componentKey 0 z [h₀, a₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, b₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, b₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, a₀, b₁]) 0,
   boundedEntry (componentKey 1 z [a₀, p₀, a₁]) 0,
   lineEntry (componentKey 1 l [h₀, b₀, a₁]) (-1 / 12)]

def bucket41 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, a₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, b₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [h₀, a₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, b₀, b₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, a₀, a₀, u₁]) 0,
   boundedEntry (componentKey 1 z [b₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 l [u₀, h₀, p₁]) 0,
   lineEntry (componentKey 1 l [a₀, a₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, h₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [h₀, p₀, a₁]) 0]

def bucket42 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, h₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, a₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, b₀, b₀, a₁]) 1,
   boundedEntry (componentKey 0 l [a₀, a₀, b₀, u₁]) 1,
   boundedEntry (componentKey 0 l [b₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, u₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, b₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 1 l [u₀, a₀, a₁]) 0,
   lineEntry (componentKey 1 l [a₀, b₀, h₁]) (-1 / 12),
   boundedEntry (componentKey 1 l [b₀, b₁]) (-1 / 12)]

def bucket43 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, h₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, h₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, h₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, a₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 l [u₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, b₀, b₀, b₀, b₁]) 1,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, h₀, a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, h₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, a₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [a₀, a₀, a₁]) 0,
   boundedEntry (componentKey 1 l [u₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [a₀, p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₁ [p₀, b₁]) 0]

def bucket44 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, h₀, h₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [a₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, b₀, b₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, a₀, p₀, p₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [h₀, h₀, h₁]) 0,
   boundedEntry (componentKey 1 z [a₀, b₀, b₁]) 0,
   lineEntry (componentKey 1 l [b₀, b₀, a₁]) (-1 / 12),
   boundedEntry (componentKey 1 e₂ [u₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, p₀, b₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, a₀, a₁]) 0]

def bucket45 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, h₀, h₀, p₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, h₀, a₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, h₀, h₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 l [a₀, b₀, b₀, b₀, u₁]) 2,
   boundedEntry (componentKey 0 e₂ [u₀, h₀, a₀, a₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, b₀, b₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [h₀, a₀, a₀, b₀, u₁]) 0,
   boundedEntry (componentKey 1 l [u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, u₀, a₁]) 0,
   boundedEntry (componentKey 1 e₂ [u₀, b₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 1 e₁ [b₀, p₀, a₁]) 0]

def bucket46 : List (Entry X) :=
  [boundedEntry (componentKey 0 z [u₀, u₀, u₀, p₀, b₁]) 0,
   boundedEntry (componentKey 0 z [u₀, u₀, h₀, a₀, a₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 z [u₀, h₀, b₀, b₁]) 0,
   boundedEntry (componentKey 0 l [u₀, u₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 l [h₀, h₀, a₀, p₀, u₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, u₀, b₀, p₁]) 0,
   boundedEntry (componentKey 0 e₂ [u₀, u₀, a₀, a₀, p₀, a₁]) 0,
   boundedEntry (componentKey 0 e₂ [h₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, u₀, h₀, p₀, h₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, h₀, h₀, h₀, u₁]) 0,
   boundedEntry (componentKey 0 e₁ [u₀, a₀, a₀, b₀, a₁]) 0,
   boundedEntry (componentKey 0 e₁ [a₀, a₀, a₀, u₁]) (-1),
   boundedEntry (componentKey 0 e₁ [a₀, b₀, b₀, p₀, u₁]) 0,
   boundedEntry (componentKey 1 z [p₀, h₁]) 0,
   boundedEntry (componentKey 1 e₁ [u₀, p₀, p₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, a₀, h₁]) 0,
   lineEntry (componentKey 1 e₁ [a₀, b₁]) 0]

def candidates : ℕ → List (Entry X)
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

/-- Return the checked entry, retaining the preceding evaluator on every miss. -/
def value (q : SurfaceAncestorKey X) : ℚ :=
  stageLookup (boundValue X) q (candidates (slot q))

theorem value_eq (q : SurfaceAncestorKey X) : value q = pointCoordinateComponent X q :=
  stageLookup_eq (boundValue X) (boundValue_eq X) q _

end AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupFirstPower
