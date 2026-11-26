/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.MixedExceptionalSingletons.SecondPower

/-! # Lower-genus vertices of cotangent power 3 in the E₁ + E₂ singleton squares

Each entry checks its full effective class and marked multiset against the original
cotangent recursion. Primitive exceptional and class-zero entries are reused.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoMixedExceptionalSingletonComponents.ThirdPower
open SurfaceGenusTwoPositiveSquare GenusTwoSecondUnitPairs
open GenusTwoSecondUnitPairs.TwoBlowupComponents

set_option Elab.async false
set_option maxRecDepth 65536

abbrev mixed : X.Curve := ![1, 1, 0]
abbrev previous := SecondPower.components

def bucket1 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [u₀, p₀, ⟨.unit, 3⟩]) 0]

def bucket4 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [p₀, u₁, u₂]) 0]

def bucket6 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [b₀, b₀, ⟨.unit, 3⟩]) 0]

def bucket7 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [u₀, p₁, u₂]) 0]

def bucket18 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [a₀, a₁, u₂]) 0]

def bucket19 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [b₀, b₁, u₂]) 0]

def bucket30 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [a₀, a₀, ⟨.unit, 3⟩]) 0]

def bucket35 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [h₀, h₁, u₂]) 0]

def bucket45 : List (Entry X) :=
  [previous.entry (componentKey 1 mixed [h₀, h₀, ⟨.unit, 3⟩]) 0]

/-- Additional certificates at this total cotangent power, indexed by full-key hash. -/
def candidates : ℕ → List (Entry X)
  | 1 => bucket1
  | 4 => bucket4
  | 6 => bucket6
  | 7 => bucket7
  | 18 => bucket18
  | 19 => bucket19
  | 30 => bucket30
  | 35 => bucket35
  | 45 => bucket45
  | _ => []

/-- Every unlisted key falls back to the certified boundary evaluation. -/
def components : CertifiedComponents X := previous.layer 3 fun i ↦
  candidates i ++ TwoBlowupCache.candidates i

end AxiomaticGW.BlowupTwoMixedExceptionalSingletonComponents.ThirdPower
