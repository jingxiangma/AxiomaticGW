/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineHComponents
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalInteriorPairs.Components
public import AxiomaticGW.Surfaces.Fixtures.RulingPairs.ShiftedDimension

/-! # Existing lower-genus components of the ruling H equations

An exact matching marked key reuses the earlier shifted strict-line H computation.
The remaining vertices retain the ruling or exceptional-face recursions. On the
plane-degree-zero face the previously proved exceptional incidence applies at
every cotangent degree.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRuling.H
open SurfaceGenusTwoPositiveSquare SurfaceLowGenusPointCache

/-- Search exactly the archived bucket for the absolute genus, effective class and marked key. -/
def strictLineEntry? (q : SurfaceAncestorKey X) : Option BlowupTwoLineH.Components.Entry :=
  let k := BlowupTwoLineH.Components.slot q
  let bucket := ((BlowupTwoLineH.Components.buckets[k/32]?.getD #[])[k%32]?).getD []
  bucket.find? (fun e ↦ decide (q = e.key))

private theorem eq_of_entry (q : SurfaceAncestorKey X) (e : BlowupTwoLineH.Components.Entry)
    (h : strictLineEntry? q = some e) : q = e.key :=
  of_decide_eq_true (List.find?_some
    (p := fun z : BlowupTwoLineH.Components.Entry ↦ decide (q = z.key)) h)

/-- Compose verified full-key hits with the existing ruling component evaluator. -/
def withStrictLine (c : CertifiedComponents X) : CertifiedComponents X where
  value q := match strictLineEntry? q with
    | some e => e.value
    | none => c.value q
  sound q := by
    split
    · rename_i e he
      rw [eq_of_entry q e he, pointCoordinateComponent, coordinateComponent_eq, e.checked,
        scalarComponentValue_eq]
    · exact c.sound q

/-- The shifted-column backend first applies exceptional incidence and then exact lower vertices. -/
def components (i : Fin 2) : CertifiedComponents X :=
  BlowupTwoDoubleExceptionalInteriorPairs.withIncidence (withStrictLine (Third.backend i))

/-- Every shifted source with the combined backend equals the very same original source. -/
theorem dimensionWeighted_components (i : Fin 2) (j : Fin 815) :
    dimensionWeighted (components i) i j = weighted (Third.backend i) i j := by
  rw [dimensionWeighted_eq]
  unfold weighted
  simp only [lowerVertex_eq_pullback, CertifiedComponents.vertex_eq]

end AxiomaticGW.BlowupTwoRuling.H
