/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoSingletons
public import AxiomaticGW.GKM.Fixtures.F1DoubleExceptionalOneMarkingReplay
public import AxiomaticGW.GKM.Fixtures.F1FiberOneMarkingReplay

/-! # Positive-plane-degree singletons on Bl₂ compared with the two energy-two sectors of F₁

The doubled strict line gives the negative exceptional-divisor value for each divisor
marking. On each ruling the unit descendant differs from the corresponding fiber value.
These statements concern the incoming Bl₂ fields and the original F₁ reconstruction.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupTwoPositivePlaneEnergyTwoSingletons
open EquivariantCoefficients SurfaceGenusTwoBlowupDescendants

/-- The curves in report order, in the effective basis E₁, E₂, L. -/
def curves : Fin 3 → SurfaceTarget.blowupTwo.Curve := ![![0,0,2], ![0,1,1], ![1,0,1]]

/-- Position of a class and basis insertion in the exact 15-row report. -/
def index (c : Fin 3) (b : Fin 5) : Fin 15 := ⟨5*c.val + b.val, by omega⟩

/-- Each basis label on each curve has the cotangent power required by virtual dimension. -/
theorem binding : ∀ (c : Fin 3) (b : Fin 5),
    let a : SurfaceBasisLabel .blowupTwo :=
      ![.unit, .hyperplane, .exceptional 0, .exceptional 1, .point] b
    requests (index c b) = ⟨2, curves c, [⟨a, 4 - a.codimension⟩]⟩ ∧
    (requests (index c b)).DimensionCompatible := by decide +kernel

/-- For 2L each of the three divisor values is the negative of the F₁ value at τ₃(E) in 2E.
The unit and the point have the same sign and value as their F₁ counterparts. -/
theorem doubled_line (b : Fin 5) :
    let k : Fin 4 := ![0,2,2,2,3] b
    let sign : ℚ := ![1,-1,-1,-1,1] b
    queryValue? 0 (F1DoubleExceptionalOneMarking.requests k) =
      some (F1DoubleExceptionalOneMarking.values k) ∧
    equivariant (index 0 b) =
      (sign : Coefficient) * F1DoubleExceptionalOneMarking.equivariant k := by
  have h : ∀ b : Fin 5, values (index 0 b) =
      (![1,-1,-1,-1,1] b : ℚ) * F1DoubleExceptionalOneMarking.values (![0,2,2,2,3] b) := by
    decide +kernel
  refine ⟨F1DoubleExceptionalOneMarking.accepted _, ?_⟩
  rw [equivariant_eq_ordinary, F1DoubleExceptionalOneMarking.equivariant_eq_ordinary,
    h, Rat.cast_mul]

/-- Choose the old unit, hyperplane, retained exceptional divisor or point on each ruling. -/
def rulingIndex (i : Fin 2) (b : Fin 4) : Fin 15 :=
  index i.succ (![0,1,(if i = 0 then 2 else 3),4] b)

/-- The H, retained exceptional and point comparisons agree with F₁. At τ₄(1) the full
incoming ruling field differs from the reconstructed fiber value by −11/1920. -/
theorem ruling (i : Fin 2) (b : Fin 4) :
    let correction : ℚ := if b = 0 then -11/1920 else 0
    queryValue? 0 (F1FiberOneMarking.requests b) = some (F1FiberOneMarking.values b) ∧
    equivariant (rulingIndex i b) =
      F1FiberOneMarking.equivariant b + (correction : Coefficient) := by
  have h : ∀ (i : Fin 2) (b : Fin 4), values (rulingIndex i b) =
      F1FiberOneMarking.values b + (if b = 0 then -11/1920 else 0) := by decide +kernel
  refine ⟨F1FiberOneMarking.accepted _, ?_⟩
  rw [equivariant_eq_ordinary, F1FiberOneMarking.equivariant_eq_ordinary, h, Rat.cast_add]

/-- The remaining exceptional state contributes a nonzero full field on both rulings. -/
theorem other_exceptional (i : Fin 2) :
    equivariant (index i.succ (if i = 0 then 3 else 2)) = 1/2880 := by
  have h : ∀ i : Fin 2, values (index i.succ (if i = 0 then 3 else 2)) = 1/2880 := by
    decide +kernel
  rw [equivariant_eq_ordinary, h]
  norm_num

end AxiomaticGW.GKM.BlowupTwoPositivePlaneEnergyTwoSingletons
