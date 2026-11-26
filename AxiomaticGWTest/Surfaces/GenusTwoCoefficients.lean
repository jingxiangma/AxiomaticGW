/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Surfaces.GenusTwoCoefficientRelations

set_option linter.privateModule false

namespace AxiomaticGWTest.Surfaces.GenusTwoCoefficients
open AxiomaticGW SurfacePolynomialReduction SurfaceGenusTwo
open RelationCertificate PsiBoundaryExpansion

-- Requested variables may have any class; equality to the input is not a hypothesis.
example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X)
    (v : Variable X) :
    BelorousskiPandharipande.normalizedCoefficient X n beta k a v =
      RationalTerms.coefficient (BelorousskiPandharipande.normalizedGenusTwoTerms
        X n beta k a) {v} := BelorousskiPandharipande.normalizedCoefficient_eq X n beta k a v

example (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (v : Variable X) :
    L24Relation.normalizedCoefficient X n beta k a v =
      RationalTerms.coefficient (L24Relation.normalizedGenusTwoTerms X n beta k a) {v} :=
  L24Relation.normalizedCoefficient_eq X n beta k a v

private abbrev genusTwoPair : GluingExpression 2 (Option (Fin 1)) :=
  .fundamental 2 _ (by norm_num [StableArity])

private abbrev rationalTriple : GluingExpression 0 (Option (Fin 2)) :=
  .fundamental 0 _ (by norm_num [StableArity])

private def zeroPoint : Variable .plane := .inr (SurfaceQuery.points .plane 2 0 1)

-- A positive-degree rational complement contributes to a smaller-class primary.
-- The divisor correction on <tau_1(H),H>_2,0 supplies N_2,0 with coefficient one.
example : coefficientEval .plane zeroPoint (genusTwoPair.separating rationalTriple)
    (by decide +kernel) ((fun s ↦ Option.elim s 0 (fun _ ↦ 1)), 0) ![1] 0
      (Sum.elim (fun _ ↦ .hyperplane) (fun _ ↦ .point)) = 1 := by decide +kernel

-- The equality theorem certifies this in the original normalized contraction.
example : normalizedCoefficient (genusTwoPair.separating rationalTriple)
    ((fun s ↦ Option.elim s 0 (fun _ ↦ 1)), 0) (![1] : SurfaceTarget.plane.Curve) 0
      (Sum.elim (fun _ ↦ .hyperplane) (fun _ ↦ .point)) zeroPoint = 1 := by
  rw [← coefficientEval_eq zeroPoint _ (by omega)]
  decide +kernel

-- Both component orientations retain the positive rational factor.
example : coefficientEval .plane zeroPoint (rationalTriple.separating genusTwoPair)
    (by decide +kernel) (0, (fun s ↦ Option.elim s 0 (fun _ ↦ 1))) ![1] 0
      (Sum.elim (fun _ ↦ .point) (fun _ ↦ .hyperplane)) = 1 := by decide +kernel

private abbrev triple : GluingExpression 2 (Fin 3) :=
  .fundamental 2 _ (by norm_num [StableArity])

private def lowerExceptionalPoint : Variable .hirzebruchOne :=
  .inr (SurfaceQuery.points .hirzebruchOne 2 ![1,0] 2)

-- A negative calibration tail at 2E is part of the coefficient at E.
example : coefficientEval .hirzebruchOne lowerExceptionalPoint triple (by decide +kernel)
    0 ![2,0] ![1,0,0] ![.exceptional 0, .point, .point] = -1 := by decide +kernel

-- Distinct equal-energy exceptional classes remain distinct through normalization.
example : coefficientEval .blowupTwo
    (.inr (SurfaceQuery.points .blowupTwo 2 ![0,1,0] 2)) triple (by decide +kernel)
    0 ![2,0,0] ![1,0,0] ![.exceptional 0, .point, .point] = 0 := by decide +kernel

private abbrev single : GluingExpression 2 (Fin 1) :=
  .fundamental 2 _ (by norm_num [StableArity])

private def higherAncestor : SurfaceAncestorKey .plane :=
  SurfaceAncestorKey.ofLabels 2 (Fin 1) single.stable ![1] (fun _ ↦ 3) (fun _ ↦ .point)

-- Unreduced higher powers retain their ancestor tag.
example : coefficientEval .plane (.inl higherAncestor) single (by decide +kernel)
    (fun _ ↦ 2) ![1] (fun _ ↦ 1) (fun _ ↦ .point) = 1 := by decide +kernel

-- Variables above the input degree have zero coefficient, rather than a truncated shift.
example : coefficientEval .plane (.inr (SurfaceQuery.points .plane 2 ![2] 7))
    (genusTwoPair.separating rationalTriple) (by decide +kernel)
    ((fun s ↦ Option.elim s 0 (fun _ ↦ 1)), 0) ![1] 0
      (Sum.elim (fun _ ↦ .hyperplane) (fun _ ↦ .point)) = 0 := by decide +kernel

end AxiomaticGWTest.Surfaces.GenusTwoCoefficients
