/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGW.Tautological.GenusTwoPsiProductGluing
import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiProductReplay

open AxiomaticGW RelationCertificate GenusTwoPsiProduct

example : AcceptsExchange GenusTwoPsiProductReplay.exchange := GenusTwoPsiProductReplay.accepted

example : (columns 5).codimension = 2 := columns_codimension 5

example : interpret columns requested ≠ 0 := requested_ne_zero

-- The genus-two contribution is part of the equation, not part of the discarded low-genus sector.
example : boundary (boundaryIndex 0) = 3 := genusTwo_tail_coefficient

example : (boundaryTerm 0).1.maxComponentGenus = 2 := by decide +kernel

example (i : Fin 25) (hi : i ≠ 0) : (boundaryTerm i).1.maxComponentGenus ≤ 1 :=
  boundaryTerm_lower_genus i hi

-- The source matrix really carries the kappa_1-squared correction.
example : pushforwardToMonomial 1 0 = 1 ∧ monomialToPushforward 1 0 = -1 := by decide +kernel

-- A self-consistent zero request cannot replace the independently held claim.
example : ¬ AcceptsExchange
    { GenusTwoPsiProductReplay.exchange with presentation :=
      { GenusTwoPsiProductReplay.exchange.presentation with
        rows := 0, claimedRequest := 0, certificate := ⟨0⟩ } } := by
  intro h
  have he := congrFun h.1.1.2.2.2 (5 : Fin 38)
  exact (zero_ne_one : (0 : ℚ) ≠ 1) he

-- Node decorations break loop-branch symmetry; raw graph stabilizers are insufficient.
example : automorphismOrders 26 = 1 ∧ automorphismOrders 25 = 2 := by decide +kernel

example : check rows requested ⟨0⟩ = false := by decide +kernel
