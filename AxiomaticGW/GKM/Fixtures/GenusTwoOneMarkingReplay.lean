/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.GenusTwoOneMarkingClaims
public import AxiomaticGW.Surfaces.PlaneGenusTwoFewMarkingBenchmarks
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1ExceptionalOneMarkingValues
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoExceptionalOneMarking

/-!
# Reconstruction of the 17 one-marking localization claims

The held rows use the line of the plane and each exceptional generator of the
two blowups. Each comparison retains its full effective class, divisor and
cotangent power. The geometric identification of the descendant algorithm
uses the inputs of its surface soundness theorem.
-/

@[expose] public section
namespace AxiomaticGW.GKM.GenusTwoOneMarking

/-- All three ordinary line descendants agree with the incoming plane queries. -/
theorem Plane.accepted (i : Fin 3) :
    BelorousskiPandharipande.planeQueryValue? (Plane.requests i) = some (Plane.values i) := by
  apply SurfaceGenusTwo.planeFewMarkingBenchmark?_sound
  fin_cases i <;> decide +kernel

/-- All four F₁ claims agree with the complete mixed descendant evaluation. -/
theorem OneBlowup.accepted (i : Fin 4) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (OneBlowup.requests i) =
      some (OneBlowup.values i) := by
  have hq : OneBlowup.requests i = BlowupF1ExceptionalOneMarkingRequest.requests i := by
    fin_cases i <;> decide +kernel
  have hv : OneBlowup.values i = BlowupF1ExceptionalOneMarkingValues.values i := by
    fin_cases i <;> decide +kernel
  rw [hq, hv]
  exact BlowupF1ExceptionalOneMarkingValues.accepted i

/-- Both exceptional curves and their five labelled descendants are certified separately. -/
theorem TwoBlowups.accepted (i : Fin 10) :
    SurfaceGenusTwoBlowupDescendants.queryValue? 0 (TwoBlowups.requests i) =
      some (TwoBlowups.values i) := by
  let curve : Fin 2 := ⟨i.val / 5, by omega⟩
  let marking : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
  have bind : TwoBlowups.requests i = BlowupTwoExceptionalOneMarking.request curve marking ∧
      TwoBlowups.values i = BlowupTwoExceptionalOneMarking.values curve marking := by
    dsimp only [curve, marking]
    clear curve marking
    revert i
    decide +kernel
  rw [bind.1, bind.2]
  exact BlowupTwoExceptionalOneMarking.accepted curve marking

end AxiomaticGW.GKM.GenusTwoOneMarking
