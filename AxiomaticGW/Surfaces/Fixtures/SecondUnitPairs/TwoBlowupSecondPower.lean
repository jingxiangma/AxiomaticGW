/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowupFirstPower

/-! # Two-power vertices in the pulled genus-two square
One original cotangent equation is checked against the first-power table.
The finite lookup keeps all effective curve coordinates and node insertions.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupSecondPower
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache TwoBlowupComponents
set_option Elab.async false
set_option maxRecDepth 65536

def previous (q : SurfaceAncestorKey X) : ℚ :=
  if q.totalPsi = 1 then TwoBlowupFirstPower.value q else boundValue X q

theorem previous_eq (q : SurfaceAncestorKey X) :
    previous q = pointCoordinateComponent X q := by
  unfold previous
  split
  · exact TwoBlowupFirstPower.value_eq q
  · exact boundValue_eq X q

def checked (q : SurfaceAncestorKey X) (v : ℚ)
    (h : v = stagedValue previous q := by decide +kernel) : Entry X :=
  stepEntry previous previous_eq q v h

def bucket0 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, a₀, a₀, u₁, b₁]) 2,
   checked (componentKey 0 e₂ [u₀, u₀, h₀, h₀, u₁, p₁]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, p₀, u₁, b₁]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, a₀, u₁, a₁]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, a₀, a₀, a₀, u₂]) 0,
   checked (componentKey 1 z [b₀, p₀, u₂]) 0,
   checked (componentKey 1 l [u₀, p₀, u₁, b₁]) 0,
   checked (componentKey 1 l [u₀, b₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₂ [u₀, h₀, h₁, a₁]) 0,
   checked (componentKey 1 e₁ [h₀, h₀, u₂]) 0]

def bucket1 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, h₀, h₀, u₂]) 2,
   checked (componentKey 0 e₂ [u₀, h₀, b₀, u₁, b₁]) 0,
   checked (componentKey 0 e₂ [u₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, a₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 l [u₀, a₀, a₁, a₁]) (-1 / 6),
   checked (componentKey 1 l [b₀, u₂]) (-1 / 24)]

def bucket2 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, h₀, h₀, u₂]) 1,
   checked (componentKey 0 l [u₀, h₀, h₀, u₁, a₁]) 2,
   checked (componentKey 0 l [u₀, b₀, b₀, b₀, u₂]) 1,
   checked (componentKey 0 e₁ [u₀, b₀, b₀, u₁, a₁]) 0,
   checked (componentKey 1 l [u₀, b₀, a₁, b₁]) (-1 / 6),
   checked (componentKey 1 l [u₀, b₀, u₂]) 0,
   checked (componentKey 1 l [a₀, a₀, u₁, h₁]) (-1 / 4),
   checked (componentKey 1 l [a₀, u₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₂ [u₀, p₀, u₁, h₁]) 0,
   checked (componentKey 1 e₂ [u₀, h₁, b₁]) 0,
   checked (componentKey 1 e₂ [h₀, u₁, a₁]) 0,
   checked (componentKey 1 e₁ [b₀, u₁, h₁]) 0,
   checked (componentKey 1 e₁ [p₀, u₂]) 0]

def bucket3 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, a₀, a₀, u₁, p₁]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, u₀, p₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, b₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, u₂]) 0,
   checked (componentKey 1 z [a₀, b₀, u₂]) 0,
   checked (componentKey 1 l [u₀, u₀, b₁, p₁]) 0,
   checked (componentKey 1 e₂ [u₀, a₁, a₁]) 0,
   checked (componentKey 1 e₂ [h₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, p₀, u₂]) 0]

def bucket4 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, h₀, h₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, a₀, a₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, b₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, b₀, b₀, p₀, u₂]) 0,
   checked (componentKey 1 l [u₀, h₀, h₁, h₁]) (-1 / 6),
   checked (componentKey 1 e₂ [a₀, u₁, h₁]) 0,
   checked (componentKey 1 e₁ [h₀, b₀, u₂]) 0]

def bucket5 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, u₀, p₀, u₂]) 1,
   checked (componentKey 0 l [u₀, u₀, p₀, u₁, a₁]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, a₀, u₁, p₁]) 0,
   checked (componentKey 0 e₂ [u₀, b₀, b₀, u₁, b₁]) (-2),
   checked (componentKey 1 l [b₀, b₀, u₁, b₁]) (-1 / 4),
   checked (componentKey 1 e₂ [u₀, u₀, h₁, p₁]) 0,
   checked (componentKey 1 e₁ [a₀, u₂]) (1 / 24)]

def bucket6 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, a₀, u₂]) 1,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, a₀, u₁, a₁]) 3,
   checked (componentKey 0 e₁ [u₀, a₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 l [h₀, u₁, h₁]) (-1 / 6),
   checked (componentKey 1 e₂ [h₀, a₀, u₂]) 0,
   checked (componentKey 1 e₂ [b₀, u₁, a₁]) 0,
   checked (componentKey 1 e₁ [u₀, a₀, a₁, b₁]) 0,
   checked (componentKey 1 e₁ [u₀, a₀, u₂]) 0]

def bucket7 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, a₀, u₂]) 0,
   checked (componentKey 0 l [u₀, u₀, u₀, p₀, p₀, u₂]) 0,
   checked (componentKey 0 l [u₀, u₀, h₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, b₀, u₁, b₁]) 0,
   checked (componentKey 1 l [u₀, h₁, a₁]) (-1 / 6),
   checked (componentKey 1 e₂ [b₀, b₀, u₁, h₁]) 0,
   checked (componentKey 1 e₂ [b₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, b₀, b₁, b₁]) 0]

def bucket8 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, u₀, b₀, b₀, u₁, p₁]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, a₀, b₀, u₂]) 0,
   checked (componentKey 1 l [h₀, h₀, u₂]) (-1 / 8),
   checked (componentKey 1 e₁ [a₀, a₀, u₁, a₁]) (1 / 4),
   checked (componentKey 1 e₁ [b₀, b₀, u₂]) 0]

def bucket9 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, a₀, p₀, u₂]) 0,
   checked (componentKey 0 l [u₀, h₀, h₀, b₀, b₀, u₂]) 2,
   checked (componentKey 0 e₁ [u₀, b₀, b₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 z [u₀, u₂]) (5 / 24),
   checked (componentKey 1 z [p₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [h₀, h₀, u₁, h₁]) 0]

def bucket10 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, b₀, b₀, u₂]) (-1),
   checked (componentKey 0 l [u₀, b₀, b₀, u₁, a₁]) 2,
   checked (componentKey 0 e₁ [u₀, u₀, h₀, h₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, p₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, a₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, a₀, a₀, u₂]) 2,
   checked (componentKey 1 z [u₀, u₀, u₂]) 0,
   checked (componentKey 1 l [b₀, u₁, h₁]) (-1 / 6),
   checked (componentKey 1 l [p₀, u₂]) 0,
   checked (componentKey 1 e₂ [a₀, b₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, h₀, h₁, a₁]) 0]

def bucket11 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, b₀, u₁, p₁]) 0,
   checked (componentKey 0 l [u₀, a₀, a₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, a₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, b₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, b₀, u₂]) 0,
   checked (componentKey 1 l [u₀, p₀, u₂]) 0,
   checked (componentKey 1 e₂ [a₀, a₀, u₁, b₁]) 0]

def bucket12 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, b₀, b₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, b₀, u₁, b₁]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, b₀, u₂]) 0,
   checked (componentKey 1 z [a₀, p₀, u₂]) 0,
   checked (componentKey 1 l [h₀, b₀, u₂]) (-1 / 8),
   checked (componentKey 1 e₁ [u₀, p₀, u₁, h₁]) 0,
   checked (componentKey 1 e₁ [u₀, h₁, b₁]) 0,
   checked (componentKey 1 e₁ [h₀, u₁, a₁]) 0]

def bucket13 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, a₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, u₀, p₀, u₁, p₁]) 0,
   checked (componentKey 1 l [a₀, u₂]) (-1 / 24),
   checked (componentKey 1 e₂ [u₀, h₀, h₁, b₁]) 0,
   checked (componentKey 1 e₂ [h₀, h₀, u₁, a₁]) 0,
   checked (componentKey 1 e₁ [u₀, a₁, a₁]) (-1 / 6),
   checked (componentKey 1 e₁ [h₀, p₀, u₂]) 0]

def bucket14 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, a₀, a₀, a₀, u₁, a₁]) 3,
   checked (componentKey 0 l [u₀, a₀, b₀, b₀, u₂]) 1,
   checked (componentKey 0 e₂ [u₀, u₀, a₀, p₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, a₀, a₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, b₀, u₁, a₁]) 0,
   checked (componentKey 1 l [u₀, a₀, a₁, b₁]) (-1 / 6),
   checked (componentKey 1 l [u₀, a₀, u₂]) 0,
   checked (componentKey 1 e₁ [a₀, u₁, h₁]) 0]

def bucket15 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, u₁, b₁]) 2,
   checked (componentKey 0 l [u₀, h₀, u₂]) 0,
   checked (componentKey 0 l [u₀, a₀, a₀, b₀, u₁, b₁]) 3,
   checked (componentKey 0 e₂ [u₀, u₀, b₀, p₀, u₁, b₁]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, a₀, a₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, a₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, b₀, b₀, u₁, b₁]) 0,
   checked (componentKey 1 z [a₀, a₀, u₂]) 0,
   checked (componentKey 1 l [u₀, b₀, b₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₂ [h₀, u₁, b₁]) 0,
   checked (componentKey 1 e₁ [u₀, u₀, h₁, p₁]) 0]

def bucket16 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, a₀, a₀, u₁, a₁]) 0,
   checked (componentKey 0 e₂ [u₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 l [a₀, a₀, u₁, a₁]) (-1 / 4),
   checked (componentKey 1 l [b₀, b₀, u₂]) (-1 / 8),
   checked (componentKey 1 e₂ [u₀, a₀, h₁, a₁]) 0,
   checked (componentKey 1 e₂ [u₀, p₀, u₁, a₁]) 0,
   checked (componentKey 1 e₂ [u₀, a₁, b₁]) 0,
   checked (componentKey 1 e₂ [u₀, u₂]) 0,
   checked (componentKey 1 e₂ [p₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [h₀, a₀, u₂]) 0,
   checked (componentKey 1 e₁ [b₀, u₁, a₁]) 0]

def bucket17 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, b₀, b₀, b₀, b₀, u₂]) 2,
   checked (componentKey 0 e₂ [u₀, a₀, b₀, u₁, b₁]) 0,
   checked (componentKey 1 l [h₀, h₀, u₁, h₁]) (-1 / 4),
   checked (componentKey 1 e₂ [u₀, u₀, u₂]) 0,
   checked (componentKey 1 e₂ [u₀, b₀, h₁, b₁]) 0,
   checked (componentKey 1 e₁ [b₀, b₀, u₁, h₁]) 0,
   checked (componentKey 1 e₁ [b₀, p₀, u₂]) 0]

def bucket18 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, h₀, h₀, u₁, p₁]) 0,
   checked (componentKey 0 l [u₀, u₀, p₀, u₁, b₁]) 0,
   checked (componentKey 0 l [u₀, h₀, a₀, u₁, a₁]) 2,
   checked (componentKey 0 l [u₀, a₀, a₀, a₀, a₀, u₂]) 2,
   checked (componentKey 0 e₂ [u₀, u₀, a₀, a₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, b₀, b₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, b₀, u₂]) 0,
   checked (componentKey 1 z [u₀, u₁, h₁]) (-1 / 4),
   checked (componentKey 1 l [u₀, h₀, h₁, a₁]) (-1 / 6),
   checked (componentKey 1 e₂ [a₀, u₁, a₁]) 0]

def bucket19 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, b₀, u₁, b₁]) 2,
   checked (componentKey 0 l [u₀, b₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, h₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, b₀, b₀, u₁, a₁]) 0,
   checked (componentKey 1 z [h₀, u₂]) 0,
   checked (componentKey 1 e₂ [u₀, u₀, a₁, p₁]) 0,
   checked (componentKey 1 e₂ [a₀, p₀, u₂]) 0,
   checked (componentKey 1 e₂ [b₀, u₁, b₁]) (-1 / 6)]

def bucket20 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, a₀, a₀, a₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, b₀, b₀, b₀, u₁, b₁]) 3,
   checked (componentKey 1 z [u₀, h₀, u₂]) (-1 / 8),
   checked (componentKey 1 l [u₀, p₀, u₁, h₁]) 0,
   checked (componentKey 1 l [u₀, h₁, b₁]) (-1 / 6),
   checked (componentKey 1 l [h₀, u₁, a₁]) (-1 / 6),
   checked (componentKey 1 e₁ [a₀, b₀, u₂]) 0]

def bucket21 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, u₀, p₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, a₀, u₁, a₁]) 0,
   checked (componentKey 1 l [u₀, a₁, a₁]) (-1 / 6),
   checked (componentKey 1 l [h₀, p₀, u₂]) 0,
   checked (componentKey 1 e₂ [b₀, b₀, u₁, a₁]) 0,
   checked (componentKey 1 e₁ [a₀, a₀, u₁, b₁]) 0]

def bucket22 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, a₀, a₀, u₂]) 1,
   checked (componentKey 0 l [u₀, a₀, b₀, u₁, a₁]) 2,
   checked (componentKey 0 e₂ [u₀, u₀, h₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, b₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, b₀, u₂]) 0,
   checked (componentKey 1 l [a₀, u₁, h₁]) (-1 / 6),
   checked (componentKey 1 e₂ [u₀, h₁, h₁]) 0,
   checked (componentKey 1 e₂ [a₀, a₀, u₂]) 0]

def bucket23 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, a₀, u₁, p₁]) 0,
   checked (componentKey 0 l [u₀, b₀, b₀, u₁, b₁]) 2,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, b₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, a₀, b₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, u₂]) 0,
   checked (componentKey 1 z [b₀, u₂]) 0,
   checked (componentKey 1 l [u₀, u₀, h₁, p₁]) 0,
   checked (componentKey 1 e₁ [u₀, h₀, h₁, b₁]) 0,
   checked (componentKey 1 e₁ [h₀, h₀, u₁, a₁]) 0]

def bucket24 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, h₀, a₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, a₀, p₀, u₁, a₁]) 0,
   checked (componentKey 1 z [u₀, b₀, u₂]) (-1 / 24),
   checked (componentKey 1 l [h₀, a₀, u₂]) (-1 / 8),
   checked (componentKey 1 l [b₀, u₁, a₁]) (-1 / 6)]

def bucket25 : List (Entry X) :=
  [checked (componentKey 0 e₁ [u₀, u₀, b₀, p₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, a₀, a₀, u₂]) 0,
   checked (componentKey 1 l [b₀, b₀, u₁, h₁]) (-1 / 4),
   checked (componentKey 1 l [b₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [h₀, u₁, b₁]) 0]

def bucket26 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, b₀, b₀, u₁, p₁]) 0,
   checked (componentKey 0 l [u₀, h₀, h₀, u₂]) 0,
   checked (componentKey 0 l [u₀, a₀, a₀, b₀, u₂]) 1,
   checked (componentKey 0 e₂ [u₀, u₀, b₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, u₁, a₁]) (-2),
   checked (componentKey 0 e₁ [u₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 e₂ [h₀, h₀, u₁, b₁]) 0,
   checked (componentKey 1 e₂ [h₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, a₀, h₁, a₁]) 0,
   checked (componentKey 1 e₁ [u₀, p₀, u₁, a₁]) 0,
   checked (componentKey 1 e₁ [u₀, a₁, b₁]) 0,
   checked (componentKey 1 e₁ [u₀, u₂]) 0,
   checked (componentKey 1 e₁ [p₀, p₀, u₂]) 0]

def bucket27 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, b₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, b₀, u₁, b₁]) 0,
   checked (componentKey 1 e₂ [u₀, h₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, u₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, b₀, h₁, b₁]) 0]

def bucket28 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, a₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, a₀, a₀, p₀, u₂]) 0,
   checked (componentKey 1 l [a₀, b₀, u₂]) (-1 / 8),
   checked (componentKey 1 e₁ [a₀, u₁, a₁]) (-1 / 6)]

def bucket29 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, a₀, u₁, a₁]) 3,
   checked (componentKey 0 e₂ [u₀, a₀, a₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, h₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, b₀, b₀, u₁, a₁]) 0,
   checked (componentKey 1 l [a₀, a₀, u₁, b₁]) (-1 / 4),
   checked (componentKey 1 e₂ [u₀, p₀, u₁, b₁]) 0,
   checked (componentKey 1 e₂ [u₀, b₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₁ [u₀, u₀, a₁, p₁]) 0,
   checked (componentKey 1 e₁ [a₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [b₀, u₁, b₁]) 0]

def bucket30 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, b₀, u₁, b₁]) 3,
   checked (componentKey 0 l [u₀, h₀, b₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, h₀, h₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, a₀, u₂]) (-1),
   checked (componentKey 0 e₁ [u₀, b₀, b₀, b₀, u₁, b₁]) 0,
   checked (componentKey 1 z [h₀, h₀, u₂]) 0,
   checked (componentKey 1 e₂ [u₀, a₀, a₁, a₁]) 0,
   checked (componentKey 1 e₂ [b₀, u₂]) (1 / 24)]

def bucket31 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, a₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, u₁, a₁]) 0,
   checked (componentKey 0 e₂ [u₀, b₀, b₀, b₀, u₂]) (-1),
   checked (componentKey 1 l [u₀, h₀, h₁, b₁]) (-1 / 6),
   checked (componentKey 1 l [h₀, h₀, u₁, a₁]) (-1 / 4),
   checked (componentKey 1 e₂ [u₀, b₀, a₁, b₁]) 0,
   checked (componentKey 1 e₂ [u₀, b₀, u₂]) 0,
   checked (componentKey 1 e₂ [a₀, a₀, u₁, h₁]) 0,
   checked (componentKey 1 e₂ [a₀, u₁, b₁]) 0,
   checked (componentKey 1 e₁ [b₀, b₀, u₁, a₁]) 0]

def bucket32 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, a₀, p₀, u₁, a₁]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, a₀, a₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, h₀, p₀, u₂]) 0,
   checked (componentKey 1 z [u₀, u₁, a₁]) (-1 / 12),
   checked (componentKey 1 z [p₀, u₂]) 0,
   checked (componentKey 1 e₂ [u₀, u₀, b₁, p₁]) 0,
   checked (componentKey 1 e₁ [u₀, h₁, h₁]) 0,
   checked (componentKey 1 e₁ [a₀, a₀, u₂]) (-1 / 8)]

def bucket33 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, b₀, p₀, u₁, b₁]) 0,
   checked (componentKey 0 l [u₀, h₀, h₀, a₀, a₀, u₂]) 2,
   checked (componentKey 0 e₂ [u₀, u₀, h₀, h₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 z [u₀, p₀, u₂]) 0,
   checked (componentKey 1 l [h₀, u₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₂ [u₀, h₀, h₁, h₁]) 0]

def bucket34 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, a₀, a₀, u₂]) (-1),
   checked (componentKey 0 l [u₀, a₀, a₀, u₁, a₁]) 2,
   checked (componentKey 0 l [u₀, b₀, b₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, p₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, a₀, u₂]) 0,
   checked (componentKey 1 z [h₀, b₀, u₂]) 0,
   checked (componentKey 1 l [u₀, a₀, h₁, a₁]) (-1 / 6),
   checked (componentKey 1 l [u₀, p₀, u₁, a₁]) 0,
   checked (componentKey 1 l [u₀, a₁, b₁]) (-1 / 6),
   checked (componentKey 1 l [u₀, u₂]) 0,
   checked (componentKey 1 l [p₀, p₀, u₂]) 0,
   checked (componentKey 1 e₂ [b₀, b₀, u₁, b₁]) (1 / 4)]

def bucket35 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, a₀, b₀, u₁, b₁]) 2,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, a₀, u₂]) 0,
   checked (componentKey 1 z [a₀, u₂]) 0,
   checked (componentKey 1 l [u₀, u₀, u₂]) 0,
   checked (componentKey 1 l [u₀, b₀, h₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₂ [h₀, u₁, h₁]) 0]

def bucket36 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, a₀, a₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, u₀, p₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, h₀, u₁, p₁]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, b₀, p₀, u₂]) 0,
   checked (componentKey 1 z [u₀, a₀, u₂]) (-1 / 24),
   checked (componentKey 1 l [a₀, u₁, a₁]) (-1 / 6),
   checked (componentKey 1 e₂ [u₀, h₁, a₁]) 0,
   checked (componentKey 1 e₁ [h₀, h₀, u₁, b₁]) 0,
   checked (componentKey 1 e₁ [h₀, u₂]) 0]

def bucket37 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, h₀, u₂]) 1,
   checked (componentKey 0 l [u₀, a₀, b₀, b₀, u₁, a₁]) 3,
   checked (componentKey 0 e₁ [u₀, h₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 l [u₀, u₀, a₁, p₁]) 0,
   checked (componentKey 1 l [a₀, p₀, u₂]) 0,
   checked (componentKey 1 l [b₀, u₁, b₁]) (-1 / 6),
   checked (componentKey 1 e₂ [h₀, h₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, h₀, u₂]) 0]

def bucket38 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, h₀, u₂]) 0,
   checked (componentKey 0 l [u₀, a₀, a₀, a₀, u₂]) 1,
   checked (componentKey 0 l [u₀, b₀, b₀, b₀, u₁, b₁]) 3,
   checked (componentKey 0 e₂ [u₀, u₀, a₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, b₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, b₀, u₂]) 0,
   checked (componentKey 1 z [b₀, b₀, u₂]) 0]

def bucket39 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, b₀, b₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, a₀, a₀, u₁, b₁]) 0,
   checked (componentKey 1 l [b₀, b₀, u₁, a₁]) (-1 / 4),
   checked (componentKey 1 e₂ [b₀, u₁, h₁]) 0,
   checked (componentKey 1 e₂ [p₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, p₀, u₁, b₁]) 0,
   checked (componentKey 1 e₁ [u₀, b₁, b₁]) 0]

def bucket40 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, h₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, u₀, b₀, u₁, p₁]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, a₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, h₀, h₀, u₂]) 0,
   checked (componentKey 1 l [u₀, h₁, h₁]) (-1 / 6),
   checked (componentKey 1 l [a₀, a₀, u₂]) (-1 / 8),
   checked (componentKey 1 e₂ [u₀, p₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, a₀, a₁, a₁]) (1 / 6),
   checked (componentKey 1 e₁ [b₀, u₂]) 0]

def bucket41 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, h₀, b₀, u₂]) 1,
   checked (componentKey 0 l [u₀, a₀, a₀, b₀, b₀, u₂]) 2,
   checked (componentKey 0 e₂ [u₀, u₀, b₀, b₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, u₁, a₁]) 0,
   checked (componentKey 0 e₁ [u₀, b₀, b₀, b₀, u₂]) 0,
   checked (componentKey 1 e₂ [h₀, b₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, b₀, a₁, b₁]) 0,
   checked (componentKey 1 e₁ [u₀, b₀, u₂]) 0,
   checked (componentKey 1 e₁ [a₀, a₀, u₁, h₁]) 0,
   checked (componentKey 1 e₁ [a₀, u₁, b₁]) 0]

def bucket42 : List (Entry X) :=
  [checked (componentKey 0 z [u₀, u₀, b₀, u₂]) 0,
   checked (componentKey 0 l [u₀, h₀, a₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, a₀, a₀, u₁, p₁]) 0,
   checked (componentKey 1 e₂ [a₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, u₀, b₁, p₁]) 0]

def bucket43 : List (Entry X) :=
  [checked (componentKey 0 e₂ [u₀, a₀, a₀, a₀, u₁, a₁]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, b₀, b₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, h₀, h₀, p₀, u₂]) 0,
   checked (componentKey 1 z [h₀, p₀, u₂]) 0,
   checked (componentKey 1 e₂ [u₀, a₀, a₁, b₁]) 0,
   checked (componentKey 1 e₂ [u₀, a₀, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, h₀, h₁, h₁]) 0]

def bucket44 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, u₀, b₀, p₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, h₀, u₁, b₁]) 0,
   checked (componentKey 0 e₂ [u₀, h₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, a₀, a₀, b₀, u₁, b₁]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, p₀, u₁, a₁]) 0,
   checked (componentKey 1 l [h₀, h₀, u₁, b₁]) (-1 / 4),
   checked (componentKey 1 l [h₀, u₂]) (-1 / 24),
   checked (componentKey 1 e₂ [u₀, b₀, b₁, b₁]) (1 / 6),
   checked (componentKey 1 e₁ [b₀, b₀, u₁, b₁]) 0]

def bucket45 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, h₀, b₀, b₀, u₂]) 1,
   checked (componentKey 0 e₁ [u₀, h₀, h₀, a₀, u₂]) 0,
   checked (componentKey 1 z [u₀, u₁, b₁]) (-1 / 12),
   checked (componentKey 1 l [u₀, h₀, u₂]) 0,
   checked (componentKey 1 e₂ [a₀, a₀, u₁, a₁]) 0,
   checked (componentKey 1 e₂ [b₀, b₀, u₂]) (-1 / 8),
   checked (componentKey 1 e₁ [h₀, u₁, h₁]) 0]

def bucket46 : List (Entry X) :=
  [checked (componentKey 0 l [u₀, a₀, b₀, u₂]) 0,
   checked (componentKey 0 e₂ [u₀, b₀, b₀, b₀, b₀, u₂]) 2,
   checked (componentKey 0 e₁ [u₀, u₀, u₀, p₀, p₀, u₂]) 0,
   checked (componentKey 0 e₁ [u₀, u₀, h₀, u₁, p₁]) 0,
   checked (componentKey 1 z [h₀, a₀, u₂]) 0,
   checked (componentKey 1 e₂ [h₀, h₀, u₁, h₁]) 0,
   checked (componentKey 1 e₁ [u₀, h₁, a₁]) 0]

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

/-- Select the table for the exact cotangent degree, including the primary fallback. -/
def value (q : SurfaceAncestorKey X) : ℚ :=
  if q.totalPsi = 2 then stageLookup (boundValue X) q (candidates (slot q)) else previous q

theorem value_eq (q : SurfaceAncestorKey X) : value q = pointCoordinateComponent X q := by
  unfold value
  split
  · exact stageLookup_eq (boundValue X) (boundValue_eq X) q _
  · exact previous_eq q

end AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupSecondPower
