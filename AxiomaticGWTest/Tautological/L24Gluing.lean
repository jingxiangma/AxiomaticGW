/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Gluing

/-! # Rejection checks for the full L24 decorated contraction -/

@[expose] public section

namespace AxiomaticGWTest.L24Gluing
open AxiomaticGW

/-- Erasing a node power cannot reuse the valid graph identification. -/
example : let G := (L24Gluing.term 1).expression.decoratedGraph (L24Gluing.term 1).decoration
    (L24Gluing.hint 1).check { G with halfEdgePsiPower := fun _ _ ↦ 0 }
      (L24Graphs.graph 1) = false := by
  decide +kernel

/-- Erasing external powers also changes the held class. -/
example : let G := (L24Gluing.term 0).expression.decoratedGraph (L24Gluing.term 0).decoration
    (L24Gluing.hint 0).check { G with legPsiPower := fun _ ↦ 0 }
      (L24Graphs.graph 0) = false := by
  decide +kernel

/-- Transporting a marking to the wrong component is rejected. -/
example : (L24Gluing.hint 0).check
    (((L24Gluing.term 0).expression.decoratedGraph (L24Gluing.term 0).decoration).relabel
      (Equiv.swap 0 2)) (L24Graphs.graph 0) = false := by
  decide +kernel

/-- Out-of-range proposed vertex images have no isomorphism authority. -/
example : ({ L24Gluing.hint 0 with vertices := [0, 2] }).check
    ((L24Gluing.term 0).expression.decoratedGraph (L24Gluing.term 0).decoration)
      (L24Graphs.graph 0) = false := by
  decide +kernel

/-- Both branches of the node are part of the checked identification. -/
example : ({ L24Gluing.hint 1 with swaps := [true] }).check
    ((L24Gluing.term 1).expression.decoratedGraph (L24Gluing.term 1).decoration)
      (L24Graphs.graph 1) = false := by
  decide +kernel

end AxiomaticGWTest.L24Gluing
