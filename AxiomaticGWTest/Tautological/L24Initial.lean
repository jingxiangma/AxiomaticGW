/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.L24Relation

/-! # Consequential checks at the BP dimension and cancellation boundary -/

@[expose] public section

namespace AxiomaticGWTest.L24Initial
open AxiomaticGW

/-- A missing lookup key has no graph-isomorphism authority. -/
example : ((L24InitialHints.lookupKey 0).2).check (L24InitialGraphs.graph 0)
    (L24InitialGraphs.graph 0) = false := by
  decide +kernel

/-- An auxiliary coefficient is nonzero before averaging and cannot simply be dropped. -/
example : L24InitialReplay.beforeAverageClaim 815 = 1 / 2 := by
  decide +kernel

/-- The prescribed average proves the cancellation of that actual auxiliary coefficient. -/
example : L24InitialGraphs.averageCoordinates L24InitialReplay.beforeAverageClaim 815 = 0 := by
  decide +kernel

/-- Zero extension agrees with an original column even at the boundary of the old frame. -/
example : L24InitialGraphs.extend L24CorrectionsReplay.initialClaim 814 =
    L24CorrectionsReplay.initialClaim 814 := by
  decide +kernel

/-- All forty-five auxiliary coordinates are zero only in the final averaged row. -/
example : ∀ i : Fin 45, L24InitialGraphs.averageCoordinates
    L24InitialReplay.beforeAverageClaim (i.natAdd 815) = 0 := by
  decide +kernel

end AxiomaticGWTest.L24Initial
