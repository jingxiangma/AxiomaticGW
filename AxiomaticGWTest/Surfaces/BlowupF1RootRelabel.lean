/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabel

/-! Independent consumers retain arbitrary component data and certified caches. -/

@[expose] public section

open AxiomaticGW
open AxiomaticGW.BlowupF1RootAssembly AxiomaticGW.BlowupF1RootRelabel

example (v : ℕ → SurfaceCotangentVertexValues X ℚ) (beta : X.Curve) (n : ℕ) :
    (L24Gluing.term 141).expression.scalarPointContraction X v
      (L24Gluing.term 141).decoration (L24Gluing.term 141).labels beta n insertions =
    (L24Gluing.term 156).expression.scalarPointContraction X v
      (L24Gluing.term 156).decoration (L24Gluing.term 156).labels beta n insertions :=
  (scalar122_eq141 v beta n).symm.trans (scalar122_eq156 v beta n)

example : originalWeighted 141 = originalWeighted 156 := by
  rw [originalWeighted141_eq_ratio122, originalWeighted156_eq_ratio122]

example (cache : SurfaceGenusTwo.ResidualCache X) :
    rootSum cache 141 = rootSum cache 156 := by
  rw [rootSum141_eq_ratio122, rootSum156_eq_ratio122]
