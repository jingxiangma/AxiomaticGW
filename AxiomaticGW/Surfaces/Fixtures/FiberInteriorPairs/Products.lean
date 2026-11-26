/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.FiberInteriorPairs.Frame
public import AxiomaticGW.Surfaces.Fixtures.CertifiedComponentLayers

/-! # First-power products in the genus-two F₁ fiber frame

The 25 weighted boundary graphs are replayed for each of the two
degree-zero products and the two positive fiber-class products.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberInteriorPairs
open SurfaceGenusTwo SurfaceGenusTwoPositiveDivisorPairs SurfaceGenusTwoPositiveSquare

def productParts : Fin 4 → Fin 25 → ℚ :=
  ![![(-1 / 320), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 960), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 480), (-161 / 12960), (-161 / 12960), (5 / 162), 0, 0, 0, 0, 0, 0, 0, (13 / 4320), 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 / 480), (-161 / 12960), (-161 / 12960), (5 / 162), 0, 0, 0, 0, 0, 0, 0, (13 / 4320), 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def productValues : Fin 4 → ℚ :=
  ![(-1 / 320),
    (-1 / 960),
    (1 / 144),
    (1 / 144)]

private def productSource (j : Fin 4) (i : Fin 25) : ℚ :=
  productGraph ((CertifiedComponents.bounded X).vertex low) (productBeta j) (productLabels j) i

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
-- Keep all 25 contracted graphs in their actual complete effective class.
private theorem product_parts (j : Fin 4) (i : Fin 25) :
    productSource j i = productParts j i := by
  fin_cases j <;> fin_cases i <;> decide +kernel

theorem product_values (j : Fin 4) :
    ancestorValue low (productKey j) = productValues j := by
  rw [product_framed, ← component_eq, ← (CertifiedComponents.bounded X).vertex_eq]
  change (∑ i, productSource j i) = _
  simp only [product_parts]
  fin_cases j <;> decide +kernel

end AxiomaticGW.BlowupF1FiberInteriorPairs
