/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoExceptionalOneMarking
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoBlowupTwoOneMarkingSquareValues

/-!
# Genus-two one-marking requests on the two exceptional curves

Both exceptional curves have energy one. So does the strict transform of the
line through the two blown-up points. Only the plane-degree-zero classes use
the boundary theorem below. The evaluator retains the full canonical recursion
on every positive-plane class.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoExceptionalOneMarking
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupDescendants

/-- The basis order in each block of five requests. -/
def labels : Fin 5 → SurfaceBasisLabel .blowupTwo :=
  ![.unit, .hyperplane, .exceptional 0, .exceptional 1, .point]

/-- The one-marking basis requests at a specified exceptional curve.
Their cotangent powers are fixed by virtual dimension. -/
def request (i : Fin 2) (j : Fin 5) : SurfaceQuery .blowupTwo :=
  ⟨2, SurfaceTarget.blowupTwo.exceptionalCurve i, [⟨labels j, 3 - (labels j).codimension⟩]⟩

/-- Full exceptional coordinates determine each stable dimension-compatible request. -/
theorem domain (i : Fin 2) (j : Fin 5) :
    (request i j).beta = SurfaceTarget.blowupTwo.exceptionalCurve i ∧
    (request i j).DimensionCompatible ∧ (request i j).GeometricDomain := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Read plane-degree-zero canonical entries directly from the established boundary. -/
def terminals (s : State .blowupTwo) : ℚ :=
  if SurfaceTarget.blowupTwo.planeDegree s.1 = 0 then
    SurfaceGenusTwoBlowupBoundary.value s.1 s.2
  else SurfaceGenusTwoBlowupRecursion.values 0 s

private theorem terminals_eq (s : State .blowupTwo) :
    terminals s = SurfaceGenusTwoBlowupRecursion.values 0 s := by
  unfold terminals
  split_ifs with h
  · exact (SurfaceGenusTwoBlowupRecursion.values_boundary 0 s h).symm
  · rfl

/-- The full mixed descendant evaluator using these exact terminals. -/
def computed (i : Fin 2) (j : Fin 5) : Option ℚ :=
  queryValueWith? terminals (request i j)

/-- The terminal lookup computes the original reconstructed value at either exceptional class. -/
theorem computed_eq (i : Fin 2) (j : Fin 5) :
    computed i j = queryValue? 0 (request i j) :=
  queryValueWith?_eq_of_table 0 _ terminals (fun s _ ↦ terminals_eq s) _ (le_refl _)

/-- At either exceptional class the point descendant vanishes, including the positive-tail
transfer and the negative first-ancestor correction. -/
theorem point_accepted (i : Fin 2) :
    queryValue? 0 (request i 4) = some 0 := by
  rw [← computed_eq]
  change queryValueWith? terminals ⟨2, SurfaceTarget.blowupTwo.exceptionalCurve i,
    [⟨.point, 1⟩]⟩ = some 0
  rw [SurfaceGenusTwo.queryValueWith?_exceptional_point]
  fin_cases i <;> decide +kernel

/-- The ordinary descendants in each exceptional class. The exceptional divisor yields a
nonzero value exactly when it carries the specified curve. -/
def value (i : Fin 2) : SurfaceBasisLabel .blowupTwo → ℚ
  | .unit => 13 / 2880
  | .exceptional j => if i = j then -1 / 240 else 0
  | _ => 0

/-- Reconstructed values in the fixture basis order. -/
def values (i : Fin 2) (j : Fin 5) : ℚ := value i (labels j)

/-- All ten ordinary descendants follow from the complete query evaluator. -/
theorem accepted (i : Fin 2) (j : Fin 5) :
    queryValue? 0 (request i j) = some (values i j) := by
  rw [← computed_eq]
  unfold computed request values
  obtain ⟨hU, hH, hD⟩ := exceptional_ancestors
    (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith terminals) i
  have hE : terminals (0, .exceptional i) = -1 / 2880 := rfl
  have hN : terminals (0, .primary) = 0 := rfl
  cases labels j with
  | point =>
    change queryValueWith? terminals ⟨2, SurfaceTarget.blowupTwo.exceptionalCurve i,
      [⟨.point, 1⟩]⟩ = some 0
    exact (computed_eq i 4).trans (point_accepted i)
  | unit =>
    rw [SurfaceGenusTwo.queryValueWith?_exceptional, ancestorValueWith]
    change some (_ + (-terminals (0, .exceptional i) - 2 * terminals (0, .primary))) =
      some (13 / 2880)
    rw [show 3 - (SurfaceBasisLabel.unit (X := .blowupTwo)).codimension = 3 by rfl, hU, hE, hN]
    norm_num
  | hyperplane =>
    rw [SurfaceGenusTwo.queryValueWith?_exceptional, ancestorValueWith]
    change some (_ + 0) = some 0
    rw [show 3 - (SurfaceBasisLabel.hyperplane (X := .blowupTwo)).codimension = 2 by rfl,
      hH, add_zero]
  | exceptional l =>
    rw [SurfaceGenusTwo.queryValueWith?_exceptional, ancestorValueWith]
    change some (_ + (if SurfaceBasisLabel.exceptional l = .exceptional i then
      -terminals (0, .exceptional i) - terminals (0, .primary) else 0)) = _
    rw [show 3 - (SurfaceBasisLabel.exceptional (X := .blowupTwo) l).codimension = 2 by rfl,
      hD l, hE, hN]
    by_cases hil : i = l
    · subst l
      norm_num [value]
    · simp only [value, if_neg hil, SurfaceBasisLabel.exceptional.injEq,
        if_neg (Ne.symm hil), zero_add]

end AxiomaticGW.BlowupTwoExceptionalOneMarking
