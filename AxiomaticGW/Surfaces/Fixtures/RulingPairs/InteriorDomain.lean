/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.RulingSingletons.Frame
public import AxiomaticGW.Surfaces.GenusTwoFewMarkingDimension

/-! # All two-marked interior shapes at energy two on the rulings of Bl₂

An interior insertion has at least two cotangent powers for a unit, at least one
for a divisor, and at least zero for a point. The virtual dimension leaves one
further cotangent power between the two markings. Thus the raised and unraised
labels determine the two insertions, and their position supplies the order.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoRulingInterior
open BlowupTwoRuling (X curve)
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants

/-- The least admissible cotangent power once the elementary marked equations are excluded. -/
def insertion (a : SurfaceBasisLabel X) (raised : Bool) : SurfaceInsertion X :=
  ⟨a, 2 - a.codimension + if raised then 1 else 0⟩

/-- The raised and unraised basis states, and both possible input orders. -/
def request (i : Fin 2) (raised other : SurfaceBasisLabel X) (raisedFirst : Bool) :
    SurfaceQuery X :=
  let r := insertion raised true
  let s := insertion other false
  ⟨2, curve i, if raisedFirst then [r, s] else [s, r]⟩

/-- The actual original two elementary marked parsers must both decline an interior request. -/
def interior (q : SurfaceQuery X) : Bool :=
  (unitPairReduction? q).isNone && (divisorPairReduction? q).isNone

/-- The 25 raised/unraised profiles in both orders on the given ruling. -/
def atRuling (i : Fin 2) : Finset (SurfaceQuery X) :=
  Finset.univ.image fun t : SurfaceBasisLabel X × SurfaceBasisLabel X × Bool ↦
    request i t.1 t.2.1 t.2.2

private def byDimension (i : Fin 2) : Finset (SurfaceQuery X) :=
  ((dimensionShapes X 2).image (fun m ↦ (⟨2, curve i, m⟩ : SurfaceQuery X))).filter
    fun q ↦ q.insertions.length = 2 ∧ interior q = true

private theorem frame_eq (i : Fin 2) : atRuling i = byDimension i := by
  fin_cases i <;> decide +kernel

/-- Fifty distinct full queries lie outside the string, dilaton and primary-divisor parsers. -/
theorem card_atRuling (i : Fin 2) : (atRuling i).card = 50 := by
  fin_cases i <;> decide +kernel

/-- Membership is exactly the original dimension and ordered parser test, for arbitrary powers. -/
theorem mem_atRuling_iff (i : Fin 2) (q : SurfaceQuery X) :
    q ∈ atRuling i ↔ q.genus = 2 ∧ q.beta = curve i ∧ q.insertions.length = 2 ∧
      q.DimensionCompatible ∧ interior q = true := by
  have he : X.effective.energy (curve i) = 2 := by fin_cases i <;> decide +kernel
  rw [frame_eq, byDimension, Finset.mem_filter]
  constructor
  · rintro ⟨h, hl, hrec⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp h
    rw [← he, mem_dimensionShapes_iff (curve i) (by omega)] at hm
    exact ⟨rfl, rfl, hl, hm.2, hrec⟩
  · rintro ⟨hg, hb, hl, hd, hrec⟩
    let z : SurfaceQuery X := ⟨2, curve i, q.insertions⟩
    have hq : z = q := (SurfaceQuery.eq_iff z q).mpr ⟨hg.symm, hb.symm, rfl⟩
    refine ⟨Finset.mem_image.mpr ⟨q.insertions, ?_, hq⟩, hl, hrec⟩
    rw [← he, mem_dimensionShapes_iff (curve i) (by omega)]
    refine ⟨hl.le, ?_⟩
    change z.DimensionCompatible
    rwa [hq]

end AxiomaticGW.BlowupTwoRulingInterior
