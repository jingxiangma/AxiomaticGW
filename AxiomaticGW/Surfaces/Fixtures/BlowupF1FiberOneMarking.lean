/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberTable
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingTransfer
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberOneMarkingAncestors

/-! # Genus-two one-marking descendants in the fiber class of the one-point blowup

The dimension equation leaves one power for each basis label. The cotangent-square
relation contracts ten lower-genus graphs for the leading ancestor. The mixed
transfer also contributes three terms in class zero for each query.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberOneMarking
open SurfaceDescendant SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupF1FiberHReduction

/-- Dimension-compatible one-marking requests in full effective degree (0, 1). -/
def requests (j : Fin 4) : SurfaceQuery target :=
  ⟨2, fiber, [⟨labels j, 4 - (labels j).codimension⟩]⟩

/-- The original ordered queries lie in the stable geometric dimension. -/
theorem domain (j : Fin 4) : (requests j).GeometricDomain ∧ (requests j).DimensionCompatible := by
  fin_cases j <;> decide +kernel

/-- Reconstructed values in the unit, hyperplane, exceptional and point order. -/
def values : Fin 4 → ℚ := ![-1/120, -7/960, -23/2880, 1/240]

set_option Elab.async false
set_option maxRecDepth 65536

private def zeroKey (r : Fin 4) : SurfaceAncestorKey target :=
  oneMarkingKey 0 (labels r) (2 - (labels r).codimension)

private def zeroValues : Fin 4 → ℚ := ![7/720, -1/960, -1/2880, 0]

private theorem zero_ancestors (r : Fin 4) : ancestorValueWith boundary (zeroKey r) =
    zeroValues r := by
  fin_cases r
  · change SurfaceGenusTwo.ancestorValue _ (oneMarkingKey 0 .unit (0+2)) = _
    rw [ancestorValue_oneMarking_square]
    decide +kernel
  all_goals decide +kernel

private def tails (j : Fin 4) : RationalTerms (SurfaceAncestorKey target) :=
  let t (c : ℚ) (r : Fin 4) := RationalTerms.term c {zeroKey r}
  (![t (-1) 0 + t (-1) 1 + t (-1) 2,
     t 1 0 + t 1 2 + t (-1) 3,
     t 1 0 + t 1 1 + t 1 3,
     t 1 1 + t (-1) 2 + t 1 3] : Fin 4 → _) j

private theorem transfer_terms (j : Fin 4) :
    oneMarkingTerms (reconstructedCalibrationMatrix target) fiber (labels j)
      (4 - (labels j).codimension) 0 =
      RationalTerms.term 1 {oneMarkingKey fiber (labels j) (4 - (labels j).codimension)} +
        tails j := by
  fin_cases j <;> decide +kernel

/-- All four full mixed descendants agree with the original blowup reconstruction. -/
theorem accepted (j : Fin 4) : queryValue? 0 (requests j) = some (values j) := by
  have bound : target.effective.energy (requests j).beta ≤ 2 := by
    change target.effective.energy fiber ≤ 2
    decide +kernel
  have hm := main_ancestors (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary) j
  change ancestorValueWith boundary _ = _ at hm
  rw [← queryValueWith?_eq_of_table 0 2 boundary
    (fun s hs ↦ (BlowupF1FiberTable.values_eq s hs).symm) _ bound,
    requests, queryValueWith?_oneMarking, transfer_terms, RationalTerms.eval_add,
    RationalTerms.eval_term, Multiset.map_singleton, Multiset.prod_singleton, map_one,
    one_mul, hm]
  have three (a b c : ℚ) (r s t : Fin 4) :
      RationalTerms.eval (ancestorValueWith boundary) (RationalTerms.term a {zeroKey r} +
        RationalTerms.term b {zeroKey s} + RationalTerms.term c {zeroKey t}) =
        a * zeroValues r + b * zeroValues s + c * zeroValues t := by
    simp only [RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
      Multiset.prod_singleton, Algebra.algebraMap_self_apply, zero_ancestors]
  fin_cases j
  · exact (congrArg (fun z ↦ some (mainValues 0 + z)) (three (-1) (-1) (-1) 0 1 2)).trans
      (by decide +kernel)
  · exact (congrArg (fun z ↦ some (mainValues 1 + z)) (three 1 1 (-1) 0 2 3)).trans
      (by decide +kernel)
  · exact (congrArg (fun z ↦ some (mainValues 2 + z)) (three 1 1 1 0 1 3)).trans
      (by decide +kernel)
  · exact (congrArg (fun z ↦ some (mainValues 3 + z)) (three 1 (-1) 1 1 2 3)).trans
      (by decide +kernel)

end AxiomaticGW.BlowupF1FiberOneMarking
