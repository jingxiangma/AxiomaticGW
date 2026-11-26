/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowupSecondPower

/-! # Three-power vertices in the pulled genus-two square
The remaining 43 genus-one entries use previously certified two-power and
first-power components. The exported lookup reuses all three checked levels.
-/

@[expose] public section
namespace AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupCache
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache TwoBlowupComponents
set_option Elab.async false
set_option maxRecDepth 65536

def checked (q : SurfaceAncestorKey X) (v : ℚ)
    (h : v = stagedValue TwoBlowupSecondPower.value q := by decide +kernel) : Entry X :=
  stepEntry TwoBlowupSecondPower.value TwoBlowupSecondPower.value_eq q v h

def bucket0 : List (Entry X) :=
  [checked (componentKey 1 e₁ [a₀, u₁, u₂]) (1 / 12)]

def bucket1 : List (Entry X) :=
  [checked (componentKey 1 e₁ [u₀, u₀, p₁, u₂]) 0]

def bucket2 : List (Entry X) :=
  [checked (componentKey 1 e₂ [u₀, a₀, a₁, u₂]) 0]

def bucket3 : List (Entry X) :=
  [checked (componentKey 1 l [h₀, h₀, u₁, u₂]) (-3 / 8),
   checked (componentKey 1 e₂ [u₀, b₀, b₁, u₂]) (-7 / 24),
   checked (componentKey 1 e₁ [b₀, b₀, u₁, u₂]) 0]

def bucket4 : List (Entry X) :=
  [checked (componentKey 1 z [u₀, u₁, u₂]) (5 / 12)]

def bucket6 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, p₀, u₁, u₂]) 0,
   checked (componentKey 1 l [u₀, b₁, u₂]) (-1 / 12)]

def bucket8 : List (Entry X) :=
  [checked (componentKey 1 l [a₀, u₁, u₂]) (-1 / 12),
   checked (componentKey 1 e₂ [u₀, h₁, u₂]) 0]

def bucket9 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, u₀, p₁, u₂]) 0]

def bucket11 : List (Entry X) :=
  [checked (componentKey 1 l [b₀, b₀, u₁, u₂]) (-3 / 8)]

def bucket12 : List (Entry X) :=
  [checked (componentKey 1 e₁ [u₀, a₀, a₁, u₂]) (-7 / 24)]

def bucket13 : List (Entry X) :=
  [checked (componentKey 1 e₁ [u₀, b₀, b₁, u₂]) 0]

def bucket17 : List (Entry X) :=
  [checked (componentKey 1 e₂ [a₀, a₀, u₁, u₂]) 0]

def bucket18 : List (Entry X) :=
  [checked (componentKey 1 e₁ [u₀, h₁, u₂]) 0]

def bucket19 : List (Entry X) :=
  [checked (componentKey 1 e₂ [u₀, h₀, h₁, u₂]) 0]

def bucket20 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, a₀, a₁, u₂]) (-7 / 24)]

def bucket21 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, b₀, b₁, u₂]) (-7 / 24),
   checked (componentKey 1 e₂ [h₀, u₁, u₂]) 0]

def bucket22 : List (Entry X) :=
  [checked (componentKey 1 e₂ [u₀, a₁, u₂]) 0]

def bucket25 : List (Entry X) :=
  [checked (componentKey 1 e₂ [b₀, u₁, u₂]) (1 / 12)]

def bucket26 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, h₁, u₂]) (-1 / 12)]

def bucket27 : List (Entry X) :=
  [checked (componentKey 1 e₁ [a₀, a₀, u₁, u₂]) (-3 / 8)]

def bucket29 : List (Entry X) :=
  [checked (componentKey 1 e₁ [u₀, h₀, h₁, u₂]) 0]

def bucket31 : List (Entry X) :=
  [checked (componentKey 1 e₁ [h₀, u₁, u₂]) 0]

def bucket32 : List (Entry X) :=
  [checked (componentKey 1 e₂ [h₀, h₀, u₁, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, a₁, u₂]) (1 / 12)]

def bucket35 : List (Entry X) :=
  [checked (componentKey 1 l [a₀, a₀, u₁, u₂]) (-3 / 8),
   checked (componentKey 1 e₂ [u₀, p₀, u₁, u₂]) 0,
   checked (componentKey 1 e₂ [u₀, b₁, u₂]) (1 / 12),
   checked (componentKey 1 e₁ [b₀, u₁, u₂]) 0]

def bucket37 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, h₀, h₁, u₂]) (-7 / 24),
   checked (componentKey 1 e₂ [a₀, u₁, u₂]) 0]

def bucket38 : List (Entry X) :=
  [checked (componentKey 1 e₂ [u₀, u₀, p₁, u₂]) 0]

def bucket39 : List (Entry X) :=
  [checked (componentKey 1 l [h₀, u₁, u₂]) (-1 / 12)]

def bucket40 : List (Entry X) :=
  [checked (componentKey 1 l [u₀, a₁, u₂]) (-1 / 12),
   checked (componentKey 1 e₂ [b₀, b₀, u₁, u₂]) (-3 / 8)]

def bucket42 : List (Entry X) :=
  [checked (componentKey 1 e₁ [h₀, h₀, u₁, u₂]) 0]

def bucket43 : List (Entry X) :=
  [checked (componentKey 1 l [b₀, u₁, u₂]) (-1 / 12)]

def bucket45 : List (Entry X) :=
  [checked (componentKey 1 e₁ [u₀, p₀, u₁, u₂]) 0,
   checked (componentKey 1 e₁ [u₀, b₁, u₂]) 0]

def candidates : ℕ → List (Entry X)
  | 0 => bucket0
  | 1 => bucket1
  | 2 => bucket2
  | 3 => bucket3
  | 4 => bucket4
  | 6 => bucket6
  | 8 => bucket8
  | 9 => bucket9
  | 11 => bucket11
  | 12 => bucket12
  | 13 => bucket13
  | 17 => bucket17
  | 18 => bucket18
  | 19 => bucket19
  | 20 => bucket20
  | 21 => bucket21
  | 22 => bucket22
  | 25 => bucket25
  | 26 => bucket26
  | 27 => bucket27
  | 29 => bucket29
  | 31 => bucket31
  | 32 => bucket32
  | 35 => bucket35
  | 37 => bucket37
  | 38 => bucket38
  | 39 => bucket39
  | 40 => bucket40
  | 42 => bucket42
  | 43 => bucket43
  | 45 => bucket45
  | _ => []

/-- Complete checked buckets used by the original square graphs. -/
def pool (i : ℕ) : List (Entry X) :=
  candidates i ++ TwoBlowupSecondPower.candidates i ++ TwoBlowupFirstPower.candidates i

end AxiomaticGW.GenusTwoSecondUnitPairs.TwoBlowupCache
