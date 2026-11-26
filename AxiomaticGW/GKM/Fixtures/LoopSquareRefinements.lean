/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase00
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase01
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase02
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase10
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase11
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase12
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase20
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase21
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase22
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase30
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase31
public import AxiomaticGW.GKM.Fixtures.LoopSquareRefinementCase32

/-! Assemble all twelve unchanged finite graph classification cases. -/

@[expose] public section
set_option autoImplicit false

namespace AxiomaticGW.GKM.LoopSquareRefinements

theorem full_classification_check :
    ∀ v : Fin 4, ∀ e : Fin 3, classificationCheck v e = true := by
  intro v e
  fin_cases v <;> fin_cases e
  · exact classification_case_0_0
  · exact classification_case_0_1
  · exact classification_case_0_2
  · exact classification_case_1_0
  · exact classification_case_1_1
  · exact classification_case_1_2
  · exact classification_case_2_0
  · exact classification_case_2_1
  · exact classification_case_2_2
  · exact classification_case_3_0
  · exact classification_case_3_1
  · exact classification_case_3_2

/-- Apply the finite computation to an arbitrary valid genus-two presentation.
Completeness is obtained from the existing enumeration theorem, not an input list. -/
theorem classification_complete (G : StableGraphCode (Fin 1))
    (hg : G.totalGenus = 2) (p : PairCandidate G) (hp : Generic G p) :
    G.isomorphic? target = true ∨ G.isomorphic? doubleLoop = true ∨
      G.isomorphic? parallel = true := by
  have hv := vertexCount_le_three G p hp
  have he := edgeCount_le_two G p hp
  have hall := full_classification_check
    (⟨G.vertexCount, by omega⟩ : Fin 4) (⟨G.edgeCount, by omega⟩ : Fin 3)
  change decide (∀ c ∈ StableGraphCode.candidates (Fin 1) 2 G.vertexCount G.edgeCount,
    classificationTest c = true) = true at hall
  let c := StableGraphCode.Candidate.ofGraph G
  have hc : c.Valid 2 := StableGraphCode.Candidate.ofGraph_valid G hg
  have hmem : c ∈ StableGraphCode.candidates (Fin 1) 2 G.vertexCount G.edgeCount :=
    (StableGraphCode.mem_candidates (Fin 1) 2 G.vertexCount G.edgeCount c).mpr hc
  have hresult := (of_decide_eq_true hall) c hmem
  rw [classificationTest, dif_pos hc] at hresult
  change (if (pairs G).Nonempty then
    G.isomorphic? target || G.isomorphic? doubleLoop || G.isomorphic? parallel
    else true) = true at hresult
  rw [if_pos ⟨p, (mem_pairs_iff G p).mpr hp⟩] at hresult
  simpa only [Bool.or_eq_true, or_assoc] using hresult

end AxiomaticGW.GKM.LoopSquareRefinements
