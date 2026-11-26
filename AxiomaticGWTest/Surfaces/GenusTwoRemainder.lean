/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoPointTails

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoRemainder
open AxiomaticGW GluingExpression SurfacePolynomialReduction SurfaceGenusTwo

-- The remainder is a full curve class for any of the three targets.
example (X : SurfaceTarget) (v : Variable X) {S : Type} [Fintype S]
    (z : CotangentTerm 2 S) (delta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v) z delta n a =
      pointCoefficient X v z (SurfaceGenusZero.variableCurve v + delta) n a :=
  remainderPointCoefficient_eq X v _ rfl z delta n a

-- A source-degree check prevents truncated subtraction from inventing a coefficient.
example (n source : ℕ) (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) :
    BelorousskiPandharipande.planePointCoefficientByRemainder n source a v =
      BelorousskiPandharipande.pointCoefficient .plane n ![source] a v :=
  BelorousskiPandharipande.planePointCoefficientByRemainder_eq n source a v

example {A : Type*} [AddCommMonoid A] (f : SurfaceTarget.plane.Curve ×
    SurfaceTarget.plane.Curve → A) :
    (∑ p ∈ SurfaceTarget.plane.splittings ![1], f p) = f (0, ![1]) + f (![1], 0) :=
  SurfaceTarget.sum_plane_splittings_one f

-- Translation preserves all four remainder splittings of E1 + E2.
example : ((SurfaceTarget.blowupTwo.splittings ![1,1,0]).image
    (fun p ↦ (![2,0,0] + p.1, p.2))).card = 4 := by decide +kernel

private def zeroPoint : Variable .plane := .inr (SurfaceQuery.points .plane 2 0 1)

private def pair : CotangentTerm 2 (Option (Fin 1)) :=
  .fundamental 2 _ (by norm_num [StableArity]) (Option.elim · 0 (fun _ ↦ 1))

private def rational : CotangentTerm 0 (Option (Fin 2)) :=
  .fundamental 0 _ (by norm_num [StableArity]) 0

-- Both orientations retain a positive-degree rational component and the d=0 divisor correction.
example : remainderPointCoefficient .plane zeroPoint (planeCoefficientVertex zeroPoint)
    (pair.separating rational) ![1] 0
      (Sum.elim (fun _ ↦ .hyperplane) (fun _ ↦ .point)) = 1 := by decide +kernel

example : remainderPointCoefficient .plane zeroPoint (planeCoefficientVertex zeroPoint)
    (rational.separating pair) ![1] 0
      (Sum.elim (fun _ ↦ .point) (fun _ ↦ .hyperplane)) = 1 := by decide +kernel

private def linePrimary : Variable .plane := .inr (SurfaceQuery.points .plane 2 ![1] 4)

private def onePsi : CotangentTerm 2 (Fin 4) :=
  .fundamental 2 _ (by norm_num [StableArity]) ![1,0,0,0]

set_option maxRecDepth 10000 in
-- All -3 comes from signed degree-one cotangent tails; dropping them gives zero.
example : remainderPointCoefficient .plane linePrimary (planeCoefficientVertex linePrimary)
    onePsi ![1] 3 ![.hyperplane, .point, .point, .point] = -3 := by
  change remainderVertex .plane linePrimary (planeCoefficientVertex linePrimary)
    3 2 (Fin 4) _ ![1,0,0,0] inferInstance ![1] ![.hyperplane, .point, .point, .point] = -3
  have hp : (![1,0,0,0] : Fin 4 → ℕ) = Pi.single 0 1 := by decide +kernel
  rw [hp, remainderVertex_onePsi_plane_line]
  change -(Nat.choose 3 2 : ℚ) * remainderVertex .plane linePrimary
    (planeCoefficientVertex linePrimary) 1 2 (Fin 4) _ 0 inferInstance 0
      (Function.update ![.hyperplane, .point, .point, .point] 0 .hyperplane) = -3
  rw [remainderVertex_plane_primary]
  decide +kernel

-- The final genus-two component cannot consume a nonzero plane remainder.
example (S : Type) [Fintype S] (h : StableArity 2 S) (k : S → ℕ)
    (l : DecidableEq S) (a : S → SurfaceBasisLabel .plane) :
    remainderVertex .plane linePrimary (planeCoefficientVertex linePrimary)
      0 2 S h k l ![1] a = 0 := by
  rw [remainderVertex_plane_zero, if_neg (by decide)]

private def exceptionalPoint : Variable .hirzebruchOne :=
  .inr (SurfaceQuery.points .hirzebruchOne 2 ![1,0] 2)

private def exceptionalPsi : CotangentTerm 2 (Fin 3) :=
  .fundamental 2 _ (by norm_num [StableArity]) ![1,0,0]

-- The blowup calibration tail is nonzero and must not use the plane cancellation.
example : remainderPointCoefficient .hirzebruchOne exceptionalPoint
    (coefficientVertex .hirzebruchOne exceptionalPoint) exceptionalPsi ![1,0] 0
      ![.exceptional 0, .point, .point] = -1 := by decide +kernel

-- Equal anticanonical energy does not make E2 an effective part of 2E1.
example (z : CotangentTerm 2 (Fin 3)) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .blowupTwo) :
    pointCoefficient .blowupTwo (.inr (SurfaceQuery.points .blowupTwo 2 ![0,1,0] 2))
      z ![2,0,0] n a = 0 := by
  apply pointCoefficient_eq_zero_of_not_le
  intro h
  have hi := h 1
  change 1 ≤ 0 at hi
  exact (Nat.not_succ_le_zero 0) hi

example : BelorousskiPandharipande.planePointCoefficientByRemainder 0 0
    ![.point, .point, .point] linePrimary = 0 := by decide +kernel

private def single : CotangentTerm 2 (Fin 1) :=
  .fundamental 2 _ (by norm_num [StableArity]) (fun _ ↦ 3)

private def highAncestor : SurfaceAncestorKey .plane :=
  SurfaceAncestorKey.ofLabels 2 (Fin 1) single.expression.stable ![1]
    (fun _ ↦ 3) (fun _ ↦ .point)

-- An unreduced higher power retains its actual ancestor variable at zero remainder.
example : remainderPointCoefficient .plane (.inl highAncestor)
    (planeCoefficientVertex (.inl highAncestor)) single 0 0 (fun _ ↦ .point) = 1 := by
  decide +kernel

private def loopSource : CotangentTerm 1 (Option (Option (Fin 0))) :=
  .fundamental 1 _ (by norm_num [StableArity]) (Option.elim · 1 (fun _ ↦ 0))

-- Total genus two from a loop has no genus-two component.
example : remainderPointCoefficient .plane linePrimary (planeCoefficientVertex linePrimary)
    loopSource.nonseparating ![1] 2 (fun s ↦ Fin.elim0 s) = 0 := by decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoRemainder
