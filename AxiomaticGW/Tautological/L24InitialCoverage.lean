/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24InitialHints

/-!
# Kernel coverage of all retained BP initial terms

Component dimension zeros are checked on the actual gluing expressions.
Every other term keeps its actual decorated graph and a verified destination.
-/

@[expose] public section

namespace AxiomaticGW.L24InitialCoverage
open RelationCertificate

set_option maxRecDepth 20000

/-- All retained terms of the psi-0 contribution have their actual graph images. -/
theorem hints_valid0 : ∀ t ∈ L24Initial.pullback,
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single 0 1) = false →
      let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single 0 1)
      (L24InitialHints.hint G).check G (L24InitialGraphs.graph
        (L24InitialHints.columnIndex G)) = true := by
  decide +kernel

/-- All retained terms of the psi-1 contribution have their actual graph images. -/
theorem hints_valid1 : ∀ t ∈ L24Initial.pullback,
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single 1 1) = false →
      let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single 1 1)
      (L24InitialHints.hint G).check G (L24InitialGraphs.graph
        (L24InitialHints.columnIndex G)) = true := by
  decide +kernel

/-- All retained terms of the psi-2 contribution have their actual graph images. -/
theorem hints_valid2 : ∀ t ∈ L24Initial.pullback,
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single 2 1) = false →
      let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single 2 1)
      (L24InitialHints.hint G).check G (L24InitialGraphs.graph
        (L24InitialHints.columnIndex G)) = true := by
  decide +kernel

/-- All retained terms of the psi-3 contribution have their actual graph images. -/
theorem hints_valid3 : ∀ t ∈ L24Initial.pullback,
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single 3 1) = false →
      let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single 3 1)
      (L24InitialHints.hint G).check G (L24InitialGraphs.graph
        (L24InitialHints.columnIndex G)) = true := by
  decide +kernel

/-- The four actual cotangent contributions, without dropping any retained graph. -/
theorem covered (k : Fin 4) : ∀ t ∈ L24Initial.pullback,
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single k 1) = false →
      let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single k 1)
      G.isomorphic? (L24InitialGraphs.graph (L24InitialHints.columnIndex G)) = true := by
  have hh : ∀ t ∈ L24Initial.pullback,
      t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single k 1) = false →
        let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single k 1)
        (L24InitialHints.hint G).check G (L24InitialGraphs.graph
          (L24InitialHints.columnIndex G)) = true := by
    fin_cases k
    · exact hints_valid0
    · exact hints_valid1
    · exact hints_valid2
    · exact hints_valid3
  intro t ht hd
  let G := (t.2.expression.decoratedGraph t.2.decoration).addLegPsi (Pi.single k 1)
  exact GraphIsomorphismHint.check_sound (L24InitialHints.hint G) G
    (L24InitialGraphs.graph (L24InitialHints.columnIndex G)) (hh t ht hd)

end AxiomaticGW.L24InitialCoverage
