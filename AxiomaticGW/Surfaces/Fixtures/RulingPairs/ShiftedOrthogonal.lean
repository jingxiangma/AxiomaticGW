/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoShiftedPrimaries
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ShiftedComponents

/-! # Orthogonal primary sewing in the first shifted ruling equation

The first ruling shifts to twice the first exceptional curve plus the strict
line. Every lower-genus component on this full class with exactly one
cotangent power vanishes for arbitrary additional marked insertions.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.H
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache SurfacePointBenchmarkCache

/-- The orthogonal splitting theorem applies to the actual shifted ruling class. -/
theorem full_one_psi_zero (q : SurfaceAncestorKey X) (hb : q.beta = shifted 0)
    (hg : q.genus ≤ 1) (hk : q.totalPsi = 1) :
    componentValue X (genusZero X) (genusOne X) q = 0 :=
  BlowupTwoShiftedPrimaries.component_zero 1 q (hb.trans (by decide +kernel)) hg hk

/-- Apply the original one-cotangent vanishing before looking up any individual vertex. -/
def orthogonalComponents (i : Fin 2) : CertifiedComponents X where
  value q := if q.genus ≤ 1 ∧ q.totalPsi = 1 ∧ q.beta = shifted 0 then 0
    else (components i).value q
  sound q := by
    split_ifs with h
    · rw [pointCoordinateComponent, coordinateComponent_eq, full_one_psi_zero q h.2.2 h.1 h.2.1]
    · exact (components i).sound q

/-- Each of the 815 shifted graphs retains precisely its original weighted contraction. -/
theorem dimensionWeighted_orthogonal (i : Fin 2) (j : Fin 815) :
    dimensionWeighted (orthogonalComponents i) i j = weighted (Third.backend i) i j := by
  rw [dimensionWeighted_eq]
  unfold weighted
  simp only [lowerVertex_eq_pullback, CertifiedComponents.vertex_eq]

end AxiomaticGW.BlowupTwoRuling.H
