/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers
public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowupCache

/-! # Lower-genus vertices of cotangent power 1 in the E₁ + E₂ singleton squares

Each entry checks its full effective class and marked multiset against the original
cotangent recursion. Primitive exceptional and class-zero entries are reused.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalSingletonComponents.FirstPower
open SurfaceGenusTwoPositiveSquare GenusTwoSecondUnitPairs
open GenusTwoSecondUnitPairs.TwoBlowupComponents

set_option Elab.async false
set_option maxRecDepth 65536

abbrev mixed : X.Curve := ![1, 1, 0]
abbrev previous := CertifiedComponents.bounded X

def bucket1 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, a₀, a₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, a₀, p₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, b₀, b₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, a₀, a₀, a₁]) 0]

def bucket2 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, h₀, h₀, b₁]) 0,
   previous.entry (componentKey 0 e₁ [u₀, u₀, p₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, h₀, h₁]) 0]

def bucket3 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [a₀, a₀, a₀, h₁]) 0,
   previous.entry (componentKey 1 mixed [h₀, h₀, p₁]) 0,
   previous.entry (componentKey 1 mixed [p₀, b₁]) 0,
   previous.entry (componentKey 1 mixed [p₀, p₀, u₁]) 0]

def bucket4 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, b₀, b₀, p₀, b₁]) 0]

def bucket5 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, u₀, p₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, h₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, b₀, a₁]) 0]

def bucket6 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, h₀, b₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, b₀, b₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, b₀, b₀, b₁]) 0,
   previous.entry (componentKey 1 e₁ [a₁]) (1 / 24),
   previous.entry (componentKey 1 mixed [u₀, p₀, p₁]) 0]

def bucket7 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, a₀, a₀, h₁]) 0,
   previous.entry (componentKey 0 e₁ [u₀, b₀, b₀, a₁]) 0]

def bucket8 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [a₀, p₁]) 0]

def bucket9 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, b₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [b₀, b₀, b₀, b₀, b₁]) 0,
   previous.entry (componentKey 1 e₂ [b₁]) (1 / 24),
   previous.entry (componentKey 1 e₂ [a₀, h₁]) 0,
   previous.entry (componentKey 1 e₂ [p₀, u₁]) 0]

def bucket10 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, b₀, b₀, b₁]) (-1),
   previous.entry (componentKey 0 mixed [h₀, b₀, b₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, a₀, a₀, b₁]) 0]

def bucket11 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [b₀, b₀, p₁]) 0]

def bucket12 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, h₀, h₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, a₀, a₀, a₁]) 0,
   previous.entry (componentKey 1 e₂ [u₀, p₁]) 0]

def bucket13 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, h₀, h₀, h₀, h₁]) 0]

def bucket14 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, a₀, a₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [b₀, b₀, b₀, h₁]) 0]

def bucket15 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, u₀, p₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, a₀, a₀, p₀, a₁]) 0]

def bucket16 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, h₀, h₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, h₀, a₁]) 0]

def bucket17 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, a₀, a₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, a₀, a₁]) 0,
   previous.entry (componentKey 1 mixed [a₀, p₀, a₁]) 0]

def bucket18 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, h₀, a₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, b₀, b₁]) 0,
   previous.entry (componentKey 1 mixed [b₀, p₀, b₁]) 0]

def bucket19 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, u₀, p₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, h₀, p₀, a₁]) 0,
   previous.entry (componentKey 1 e₁ [b₁]) 0,
   previous.entry (componentKey 1 e₁ [p₀, u₁]) 0]

def bucket20 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, b₀, b₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, b₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, b₀, b₀, a₁]) 0]

def bucket21 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, a₀, a₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, a₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, b₀, b₀, h₁]) 0]

def bucket22 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, h₀, h₀, h₁]) 0,
   previous.entry (componentKey 1 e₁ [u₀, p₁]) 0]

def bucket23 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, b₀, p₀, a₁]) 0,
   previous.entry (componentKey 1 mixed [p₀, h₁]) 0]

def bucket24 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, b₀, b₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, b₀, b₀, a₁]) 0]

def bucket25 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, u₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, a₀, a₀, b₁]) 0,
   previous.entry (componentKey 1 z [u₁]) (5 / 24)]

def bucket26 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [a₀, b₀, b₀, h₁]) 0]

def bucket27 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, h₀, h₀, h₀, a₁]) 0]

def bucket28 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, a₀, a₀, p₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [b₀, b₀, b₀, a₁]) 0,
   previous.entry (componentKey 1 mixed [p₁]) 0]

def bucket29 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, h₀, h₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [b₀, b₀, b₀, b₀, h₁]) 0,
   previous.entry (componentKey 1 e₂ [h₁]) 0]

def bucket30 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, b₀, b₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, h₀, h₀, p₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, a₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, a₀, a₀, h₁]) 0]

def bucket31 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, a₀, a₀, a₁]) (-1)]

def bucket32 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, h₀, h₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, h₀, p₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, a₀, a₁]) 0]

def bucket33 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, u₀, p₀, p₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, b₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, b₀, b₀, b₁]) 0]

def bucket34 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, a₀, a₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, a₀, a₀, h₁]) 0,
   previous.entry (componentKey 1 mixed [h₀, p₀, h₁]) 0]

def bucket35 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, u₀, p₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, a₀, p₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, b₀, b₀, a₁]) 0,
   previous.entry (componentKey 1 mixed [a₀, a₀, p₁]) 0]

def bucket36 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, h₀, h₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, b₀, p₀, b₁]) 0]

def bucket37 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, b₀, b₀, b₁]) 0,
   previous.entry (componentKey 1 mixed [p₀, a₁]) 0]

def bucket38 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, b₀, b₀, p₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, b₀, h₁]) 0]

def bucket39 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, u₀, p₀, a₁]) 0,
   previous.entry (componentKey 1 e₁ [h₁]) 0,
   previous.entry (componentKey 1 mixed [h₀, p₁]) 0]

def bucket40 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, b₀, b₀, h₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, h₀, h₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, b₀, b₀, a₁]) 0,
   previous.entry (componentKey 1 e₂ [h₀, h₁]) 0]

def bucket41 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [b₀, b₀, b₀, b₁]) 0]

def bucket43 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [u₀, h₀, h₀, p₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [b₀, b₀, b₀, b₀, a₁]) 0,
   previous.entry (componentKey 1 e₂ [a₁]) 0,
   previous.entry (componentKey 1 mixed [b₀, p₁]) 0]

def bucket44 : List (Entry X) :=
  [previous.entry (componentKey 0 e₂ [u₀, b₀, b₀, a₁]) 0,
   previous.entry (componentKey 0 e₁ [u₀, a₀, a₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [a₀, a₀, a₀, a₀, a₁]) 0,
   previous.entry (componentKey 1 e₂ [b₀, h₁]) 0]

def bucket45 : List (Entry X) :=
  [previous.entry (componentKey 0 mixed [h₀, h₀, a₀, b₁]) 0,
   previous.entry (componentKey 0 mixed [h₀, h₀, a₀, a₀, h₁]) 0]

def bucket46 : List (Entry X) :=
  [previous.entry (componentKey 0 e₁ [u₀, h₀, h₀, a₁]) 0,
   previous.entry (componentKey 0 mixed [u₀, u₀, p₀, p₀, b₁]) 0]

/-- Additional certificates at this total cotangent power, indexed by full-key hash. -/
def candidates : ℕ → List (Entry X)
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
  | 43 => bucket43
  | 44 => bucket44
  | 45 => bucket45
  | 46 => bucket46
  | _ => []

/-- Every unlisted key falls back to the certified boundary evaluation. -/
def components : CertifiedComponents X := previous.layer 1 fun i ↦
  candidates i ++ TwoBlowupFirstPower.candidates i

end AxiomaticGW.BlowupTwoMixedExceptionalSingletonComponents.FirstPower
