/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.GKM.Fixtures.CurveReplay
import AxiomaticGW.GKM.Fixtures.SurfaceReplay

set_option linter.privateModule false

/-!
# Full curve and invariant-edge replay regressions

The positive examples use arbitrary effective classes and the accepted state
tables. The negative examples prove non-acceptance of concrete corruptions,
including two exceptional classes having identical energy.
-/

namespace AxiomaticGWTest.GKM.CurveReplay

open AxiomaticGW AxiomaticGW.GKM CurveConventionCertificate Matrix EquivariantCoefficients

example (beta : SurfaceTarget.plane.Curve) :
    CurveReplay.Plane.tables.curveMatrix *ᵥ (fun i ↦ (beta i : ℤ)) =
      SurfaceTarget.plane.latticeCoordinates beta :=
  CurveReplay.Plane.accepted.transport_correct beta

example (a b : SurfaceTarget.hirzebruchOne.Curve) :
    CurveReplay.OneBlowup.tables.curveMatrix *ᵥ (fun i ↦ ((a+b) i : ℤ)) =
      CurveReplay.OneBlowup.tables.curveMatrix *ᵥ (fun i ↦ (a i : ℤ)) +
        CurveReplay.OneBlowup.tables.curveMatrix *ᵥ (fun i ↦ (b i : ℤ)) :=
  CurveReplay.OneBlowup.accepted.transport_add a b

example (beta : SurfaceTarget.blowupTwo.Curve) :
    WeightedCurveClass.energy CurveReplay.TwoBlowups.tables.weights beta =
      SurfaceTarget.blowupTwo.effective.energy beta :=
  CurveReplay.TwoBlowups.accepted.energy_correct beta

-- Equal energy does not permit exchanging the two exceptional Novikov monomials.
example : SurfaceTarget.blowupTwo.effective.energy ![1,0,0] =
    SurfaceTarget.blowupTwo.effective.energy ![0,1,0] := by decide

example :
    CurveReplay.TwoBlowups.tables.curveMatrix *ᵥ (fun i ↦ ((![(1 : ℕ),0,0] i : ℤ))) ≠
      CurveReplay.TwoBlowups.tables.curveMatrix *ᵥ (fun i ↦ ((![(0 : ℕ),1,0] i : ℤ))) := by
  intro h
  have hclasses := CurveReplay.TwoBlowups.accepted.transport_injective h
  exact (by decide : (![(1 : ℕ),0,0] : Fin 3 → ℕ) ≠ ![0,1,0]) hclasses

example :
    (CurveReplay.OneBlowup.tables.intersections 1 3 : Coefficient) =
      ∑ p, SurfaceReplay.OneBlowup.tables.restrictions p 2 *
        divisorRestriction CurveFrames.OneBlowup.request p 3 /
          SurfaceReplay.OneBlowup.tables.euler p :=
  CurveReplay.OneBlowup.accepted.intersection_trace SurfaceReplay.OneBlowup.accepted 1 3

-- The complete sum specializes despite the poles of its fixed-point terms.
example : Specializes
    (∑ p, CurveFrames.OneBlowup.request.state.restrictions p 2 *
      divisorRestriction CurveFrames.OneBlowup.request p 3 /
        CurveFrames.OneBlowup.request.state.euler p) (-1) :=
  CurveReplay.OneBlowup.accepted.intersections_specialize 1 3

example :
    SurfaceTarget.hirzebruchOne.divisorPairing (SurfaceCohomology.firstChernDivisor 1)
      (CurveReplay.OneBlowup.tables.edges 2).curve =
        ((2 + (CurveReplay.OneBlowup.tables.edges 2).normalDegree : ℤ) : ℚ) :=
  CurveReplay.OneBlowup.accepted.edge_firstChern 2

def wrongExceptional : Tables .blowupTwo 5 5 :=
  { CurveReplay.TwoBlowups.tables with edges := fun e ↦
    if e = 2 then { CurveReplay.TwoBlowups.tables.edges e with curve := ![0,1,0] }
    else CurveReplay.TwoBlowups.tables.edges e }

example : ¬Accepts CurveFrames.TwoBlowups.request wrongExceptional := by
  intro h
  have hne : (wrongExceptional.edges 2).curve ≠
      wrongExceptional.wallClasses (wrongExceptional.edges 2).wall := by decide
  exact hne (h.edge_classes 2)

def wrongNormalDegree : Tables .hirzebruchOne 4 4 :=
  { CurveReplay.OneBlowup.tables with edges := fun e ↦
    if e = 2 then { CurveReplay.OneBlowup.tables.edges e with normalDegree := 0 }
    else CurveReplay.OneBlowup.tables.edges e }

example : ¬Accepts CurveFrames.OneBlowup.request wrongNormalDegree := by
  intro h
  have hne : SurfaceTarget.hirzebruchOne.c1Degree (wrongNormalDegree.edges 2).curve ≠
      2 + (wrongNormalDegree.edges 2).normalDegree := by decide
  exact hne (h.normal_energy 2)

def wrongWeight : Tables .blowupTwo 5 5 :=
  { CurveReplay.TwoBlowups.tables with edges := fun e ↦
    if e = 2 then { CurveReplay.TwoBlowups.tables.edges e with weight := ![-1,1] }
    else CurveReplay.TwoBlowups.tables.edges e }

example : ¬Accepts CurveFrames.TwoBlowups.request wrongWeight := by
  intro h
  have ht : CurveFrames.TwoBlowups.request.points (wrongWeight.edges 2).source 0 ≠
      (wrongWeight.edges 2).wall := by decide
  have hne : (wrongWeight.edges 2).weight ≠
      CurveFrames.TwoBlowups.request.tangent (wrongWeight.edges 2).source 0 := by decide
  exact hne (h.source_weights 2 0 ht)

example : ¬Accepts CurveFrames.Plane.request
    { CurveReplay.Plane.tables with curveMatrix := 0 } := by
  intro h
  have hne : (0 : Matrix (Fin 1) (Fin 1) ℤ) ≠ latticeMatrix .plane := by decide
  exact hne h.matrix_eq

noncomputable def wrongEulerRequest : Request .plane 3 3 :=
  { CurveFrames.Plane.request with state :=
    { CurveFrames.Plane.request.state with euler := fun p ↦
      2 * CurveFrames.Plane.request.state.euler p } }

example : ¬Accepts wrongEulerRequest CurveReplay.Plane.tables := by
  intro h
  have heq := h.state_euler 0
  change (2 : Coefficient) * CurveFrames.Plane.request.state.euler 0 =
    character (CurveFrames.Plane.request.tangent 0 0) *
      character (CurveFrames.Plane.request.tangent 0 1) at heq
  rw [← CurveReplay.Plane.accepted.state_euler 0] at heq
  change (2 : Coefficient) * (x*y) = x*y at heq
  have hp : x*y ≠ 0 := mul_ne_zero x_ne_zero y_ne_zero
  have heq' : (2 : Coefficient) = 1 :=
    mul_right_cancel₀ hp (by simpa only [one_mul] using heq)
  have hsum : (1 : Coefficient) + 1 = (1 : Coefficient) + 0 :=
    one_add_one_eq_two.trans (heq'.trans (add_zero _).symm)
  exact one_ne_zero (add_left_cancel hsum)

end AxiomaticGWTest.GKM.CurveReplay
