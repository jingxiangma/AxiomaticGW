/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementData

/-! One of the twelve unchanged finite classification checks. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSquareRefinements

open scoped BigOperators

/-- With three vertices and two edges both cycle ranks vanish. Global genus two
and contracted-fibre genus one are then incompatible, independently of incidence. -/
theorem classification_case_3_2 : classificationCheck 3 2 = true := by
  unfold classificationCheck
  apply decide_eq_true
  intro c hc
  have hvalid : c.Valid 2 :=
    (StableGraphCode.mem_candidates (Fin 1) 2 3 2 c).mp hc
  rw [classificationTest, dif_pos hvalid]
  have hnone : ¬ (pairs (c.toGraph hvalid)).Nonempty := by
    rintro ⟨p, hp⟩
    have hgeneric := (mem_pairs_iff (c.toGraph hvalid) p).mp hp
    have hglobal := hvalid.2.2.2
    have hfibre := hgeneric.1.2
    change (∑ v : Fin 3, c.genus v) + (2 - 1 + 1 - 3) = 1 at hfibre
    omega
  rw [if_neg hnone]

end AxiomaticGW.GKM.LoopSquareRefinements
