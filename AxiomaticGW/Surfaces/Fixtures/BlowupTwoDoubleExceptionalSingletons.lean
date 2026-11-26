/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalRemainingAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoDoubleExceptionalPairs

/-! # Complete genus-two basis singletons at 2E₁ and 2E₂ on the two-point blowup

Dimension fixes the marking power from its basis state. The hyperplane and the other
exceptional divisor have no positive tails. The unit has four calibration terms.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoDoubleExceptionalSingletons
open SurfaceDescendant SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants
open BlowupTwoDoubleExceptionalDivisor (beta calibrationTails eval_calibrationTails)
open BlowupTwoExceptionalPlaneZeroTable (table table_eq)

/-- The singleton in its unique dimension-compatible cotangent power at twice the selected axis. -/
def request (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) : SurfaceQuery .blowupTwo :=
  ⟨2, beta i, [⟨a, 4 - a.codimension⟩]⟩

/-- The complete scalar assignment on the basis of the two-point blowup. -/
def value (i : Fin 2) : SurfaceBasisLabel .blowupTwo → ℚ
  | .unit => 13/3840
  | .exceptional j => if i = j then 3/320 else 0
  | _ => 0

/-- Every displayed request lies in the original bounded, dimension-compatible benchmark. -/
theorem domain (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) : FewMarkingQuery (request i a) := by
  unfold FewMarkingQuery
  fin_cases i <;> cases a <;> first | decide +kernel | rename_i j; fin_cases j <;> decide +kernel

/-- Every dimension-compatible basis singleton at this full class is one of these requests. -/
theorem exhaustive (i : Fin 2) {q : SurfaceQuery .blowupTwo} (hg : q.genus = 2)
    (hb : q.beta = beta i) (hn : q.insertions.length = 1) (hd : q.DimensionCompatible) :
    ∃! a, q = request i a := by
  rcases q with ⟨g, b, m⟩
  change g = 2 at hg
  change b = beta i at hb
  subst g b
  obtain ⟨⟨a, k⟩, rfl⟩ := List.length_eq_one_iff.mp hn
  have he : SurfaceTarget.blowupTwo.effective.energy (beta i) = 2 := by
    fin_cases i <;> decide +kernel
  change (↑((∑ j : Fin 1, _) : ℕ) : ℤ) =
    (↑(SurfaceTarget.blowupTwo.effective.energy (beta i)) : ℤ) + 2 - 1 + 1 at hd
  rw [Fin.sum_univ_one, he] at hd
  change (↑(a.codimension + k) : ℤ) = _ at hd
  have hk : k = 4 - a.codimension := by omega
  subst k
  refine ⟨a, rfl, ?_⟩
  intro c hc
  have ht := congrArg SurfaceQuery.insertions hc
  exact (congrArg SurfaceInsertion.label (List.cons.inj ht).1).symm

set_option maxRecDepth 65536

private theorem divisor_transfer (i : Fin 2) (f : Bool) : let a := disjointDivisor i f
    oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo) (beta i) a 3 0 =
      RationalTerms.term 1 {oneMarkingKey (beta i) a 3} := by
  fin_cases i <;> cases f <;> decide +kernel

private theorem unit_transfer (i : Fin 2) :
    oneMarkingTerms (reconstructedCalibrationMatrix .blowupTwo) (beta i) .unit 4 0 =
      RationalTerms.term 1 {oneMarkingKey (beta i) .unit 4} +
        calibrationTails i (-1) (3/4) (-2) (1/2) := by
  fin_cases i <;> decide +kernel

private theorem divisor_accepted (i : Fin 2) (f : Bool) : queryValue? 0
    (request i (disjointDivisor i f)) = some 0 := by
  have hp : 4 - (disjointDivisor i f).codimension = 3 := by cases f <;> rfl
  have hm := divisor_ancestor (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) i f
  change ancestorValueWith table _ = 0 at hm
  rw [← queryValueWith?_eq_of_table 0 _ table (fun s _ ↦ table_eq s) _ (le_refl _), request, hp,
    queryValueWith?_oneMarking, divisor_transfer, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul, hm]

private theorem unit_accepted (i : Fin 2) : queryValue? 0 (request i .unit) = some (13/3840) := by
  have hm := unit_ancestor (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith table) i
  change ancestorValueWith table _ = _ at hm
  rw [← queryValueWith?_eq_of_table 0 _ table (fun s _ ↦ table_eq s) _ (le_refl _), request,
    show 4 - (SurfaceBasisLabel.unit (X := .blowupTwo)).codimension = 4 by rfl,
    queryValueWith?_oneMarking, unit_transfer, RationalTerms.eval_add, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul, hm, eval_calibrationTails]
  decide +kernel

/-- The ten full-class basis singletons, evaluated by the original mixed reconstruction. -/
theorem accepted (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) :
    queryValue? 0 (request i a) = some (value i a) := by
  cases a with
  | unit => exact unit_accepted i
  | hyperplane => exact divisor_accepted i false
  | point => exact BlowupTwoDoubleExceptionalPairs.point_accepted i
  | exceptional j =>
    by_cases h : i = j
    · subst j
      rw [value, if_pos rfl]
      exact BlowupTwoDoubleExceptionalDivisor.accepted i
    · have hj : j = i.rev := by fin_cases i <;> fin_cases j <;> first | rfl | contradiction
      rw [value, if_neg h, hj]
      exact divisor_accepted i true

/-- All singletons use the mixed arithmetic witness of the original reconstruction. -/
theorem checked (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) :
    CheckedDescendant 0 (request i a) (value i a) := .mixed (accepted i a)

/-- Their ordinary geometric values under the original reconstruction hypotheses. -/
theorem accepted_from_geometry (i : Fin 2) (a : SurfaceBasisLabel .blowupTwo) :
    type_of% (@SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
      (X := .blowupTwo) (i := 0) (q := request i a) (hg := rfl) (hv := checked i a)) :=
  @SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry
    (X := .blowupTwo) (i := 0) (q := request i a) (hg := rfl) (hv := checked i a)

end AxiomaticGW.BlowupTwoDoubleExceptionalSingletons
