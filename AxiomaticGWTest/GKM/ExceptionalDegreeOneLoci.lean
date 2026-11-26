module

import AxiomaticGW.GKM.Fixtures.ExceptionalDegreeOneLoci

set_option linter.privateModule false

namespace AxiomaticGWTest.GKM.ExceptionalDegreeOneLoci
open AxiomaticGW.GKM
open AxiomaticGW.GKM.ExceptionalDegreeOneLoci
open CurveReplay.TwoBlowups (tables)

private def reversed := FixedGraphSupport.singleCover tables 2 1 true

private theorem reversed_degree : reversed.degree = ![1, 0, 0] := by
  rw [reversed, FixedGraphSupport.degree_singleCover]
  decide +kernel

private def tagged : Decoration 2 1 := ⟨(![0, 2], 0), by decide +kernel⟩

-- The native source carries genus two at raw vertex 1. Raw vertex 0 is the marked target.
example : decorationEquiv reversed reversed_degree tagged = (2, 1) := by
  let idx := decorationEquiv reversed reversed_degree tagged
  obtain ⟨genusBinding, markBinding⟩ := index_binding reversed reversed_degree tagged
  have raw : ∀ w : Fin 2, reversed.image w = 1 ↔ w = 1 := by
    rw [reversed]
    decide +kernel
  have source : ends reversed reversed_degree 0 = 1 :=
    (raw _).mp (ends_image reversed reversed_degree 0)
  have hg := genusBinding 0
  rw [source] at hg
  change 2 = idx.1.val at hg
  have hm := (ends_image reversed reversed_degree idx.2).symm.trans
    (congrArg reversed.image markBinding)
  have target : ∀ p : Fin 2, (![1, 2] : Fin 2 → Fin 5) p = 2 ↔ p = 1 := by decide +kernel
  exact Prod.ext (Fin.ext hg.symm) ((target _).mp hm)

example : Nat.card (Decoration 2 1) = 6 := six_decorations reversed reversed_degree

end AxiomaticGWTest.GKM.ExceptionalDegreeOneLoci
