/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberOneMarking
public import AxiomaticGW.Surfaces.GenusTwoBlowupUnitPairs

/-! # Marked-equation reductions for genus-two pairs in the fiber class on F₁

The string and dilaton equations remove one marking. The divisor equation
uses both the intersection against the fiber and the signed cup correction.
Every nonvanishing singleton term uses the certified mixed reconstruction
at full curve class (0, 1). The existing geometric interpretation of these
two reduction algorithms uses the original descendant and reconstruction laws.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberMarkedPairs
open SurfaceGenusTwo SurfaceGenusTwoBlowupDescendants BlowupF1FiberHReduction

/-- The surviving fiber singleton at its dimension-compatible power. -/
def survivor (k : Fin 4) : SurfaceInsertion target :=
  ⟨BlowupF1FiberOneMarking.labels k, 4 - (BlowupF1FiberOneMarking.labels k).codimension⟩

private theorem singleton (k : Fin 4) : queryValue? 0 ⟨2, fiber, [survivor k]⟩ =
    some (BlowupF1FiberOneMarking.values k) := BlowupF1FiberOneMarking.accepted k

/-- The ordered string or dilaton pair with the indicated surviving singleton. -/
def unitRequest (rule : UnitEquation) (last : Bool) (k : Fin 4) : SurfaceQuery target :=
  rule.pair last fiber (survivor k)

/-- The recognized unit equation multiplies the original singleton by one or three. -/
theorem unit_accepted (rule : UnitEquation) (last : Bool) (k : Fin 4) :
    unitPairValue? 0 (unitRequest rule last k) =
      some (rule.factor * BlowupF1FiberOneMarking.values k) := by
  have hr : unitPairReduction? (unitRequest rule last k) = some (rule, survivor k) := by
    cases rule <;> cases last <;> fin_cases k <;> decide +kernel
  have hb : (unitRequest rule last k).beta = fiber := by cases rule <;> rfl
  simp only [unitPairValue?, hr, hb, singleton, Option.map_some]

/-- Positions of H and E in the certified singleton frame. -/
def divisorIndex : Fin 2 → Fin 4 := ![1, 2]

/-- Insert either the pullback hyperplane or the exceptional divisor, in either order. -/
def divisorRequest (d : Fin 2) (last : Bool) (k : Fin 4) : SurfaceQuery target :=
  divisorPair last fiber (BlowupF1FiberOneMarking.labels (divisorIndex d)) (survivor k)

private def cupIndex (d : Fin 2) (k : Fin 4) : Fin 4 := if k = 0 then divisorIndex d else 3

/-- The two divisor rows, with columns in unit, H, E and point order. -/
def divisorValues (d : Fin 2) (k : Fin 4) : ℚ :=
  (![![-1/64, -1/320, -23/2880, 1/240],
     ![-47/2880, -7/960, -7/576, 1/240]] : Fin 2 → Fin 4 → ℚ) d k

/-- Both signed terms in each accepted divisor reduction are actual fiber singletons. -/
theorem divisor_accepted (d : Fin 2) (last : Bool) (k : Fin 4) :
    divisorPairValue? 0 (divisorRequest d last k) = some (divisorValues d k) := by
  let a := BlowupF1FiberOneMarking.labels (divisorIndex d)
  have hr : divisorPairReduction? (divisorRequest d last k) = some (a, survivor k) := by
    cases last <;> fin_cases d <;> fin_cases k <;> decide +kernel
  have hc : cupCoefficient a (survivor k) ≠ 0 →
      cupInsertion a (survivor k) = survivor (cupIndex d k) := by
    fin_cases d <;> fin_cases k <;> decide +kernel
  have h := divisorPairValueWith?_of_singletons (queryValue? 0) (divisorRequest d last k) a
    (survivor k) (BlowupF1FiberOneMarking.values k) (BlowupF1FiberOneMarking.values (cupIndex d k))
    hr (fun _ ↦ singleton k) (fun hz ↦ (hc hz) ▸ singleton (cupIndex d k))
  refine h.trans (congrArg some ?_)
  change a.primaryFactor fiber * _ + _ = _
  fin_cases d <;> fin_cases k <;> decide +kernel

end AxiomaticGW.BlowupF1FiberMarkedPairs
