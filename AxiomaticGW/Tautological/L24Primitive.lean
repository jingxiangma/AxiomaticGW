/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.Fixtures.L24CorrectionsReplay

/-!
# The independently held primitive target of L24

The four diagrams are transcribed from Wennink, arXiv:2210.04038, section 4.
Their raw coefficients are 1, 3, -3, -3, followed by the sixfold marking
average. The checks below fix this research target independently of the
incoming full coefficient vector. They do not discard its other 703 terms.
-/

@[expose] public section

namespace AxiomaticGW.L24Primitive
open RelationCertificate

set_option maxRecDepth 20000

open StrataOperation L24CorrectionsReplay

/-- The four specified primitive decorated diagrams. -/
def picture : Fin 4 → DecoratedStableGraph (Fin 4) :=
  ![{ graph :=
        ({ legVertex := ![1, 0, 2, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![2, 0, 0] } :
          StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
      kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
      halfEdgePsiPower := ![![1, 0], ![0, 0]] },
    { graph :=
        ({ legVertex := ![0, 2, 1, 2], endpoint := ![![0, 1], ![1, 2]], genus := ![2, 0, 0] } :
          StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
      kappaPower := fun _ ↦ 0, legPsiPower := ![1, 0, 0, 0],
      halfEdgePsiPower := ![![0, 0], ![0, 0]] },
    { graph :=
        ({ legVertex := ![1, 1, 2, 2], endpoint := ![![0, 1], ![0, 2]], genus := ![2, 0, 0] } :
          StableGraphCode.Candidate (Fin 4) 3 2).toGraph (g := 2) (by decide +kernel),
      kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
      halfEdgePsiPower := ![![0, 0], ![1, 0]] },
    { graph :=
        ({ legVertex := ![1, 3, 2, 3], endpoint := ![![0, 1], ![1, 2], ![2, 3]], genus := ![2, 0, 0,
          0] } :
          StableGraphCode.Candidate (Fin 4) 4 3).toGraph (g := 2) (by decide +kernel),
      kappaPower := fun _ ↦ 0, legPsiPower := ![0, 0, 0, 0],
      halfEdgePsiPower := ![![0, 0], ![0, 0], ![0, 0]] }]

/-- All four diagrams are stable genus-two graphs. -/
theorem picture_totalGenus (i : Fin 4) : (picture i).graph.totalGenus = 2 := by
  revert i
  decide +kernel

/-- The raw diagram coefficients, prior to the specified marking average. -/
def coefficients : Coordinates 4 := ![1, 3, -3, -3]

/-- Proposed locations of the four independently specified diagrams. -/
def destination : Fin 4 → Fin 815 := ![51, 57, 52, 109]

/-- The four diagrams really are the indicated full decorated frame columns. -/
theorem pictures_covered : ∀ i, (picture i).isomorphic?
    (L24Graphs.graph (destination i)) = true := by
  decide +kernel

/-- A primitive term has one genus-two component and only undecorated trivalent rational others. -/
def primitive (i : Fin 815) : Bool :=
  let G := L24Graphs.graph i
  decide ((∃ v, G.graph.genus v = 2) ∧ ∀ v, G.graph.genus v = 2 ∨
    (G.graph.genus v = 0 ∧
      Fintype.card {s : Fin 4 // G.graph.legVertex s = v} +
        Fintype.card {p : Fin G.graph.edgeCount × Fin 2 // G.graph.endpoint p.1 p.2 = v} = 3 ∧
      G.kappaPower v = 0 ∧ (∀ s, G.graph.legVertex s = v → G.legPsiPower s = 0) ∧
      ∀ e b, G.graph.endpoint e b = v → G.halfEdgePsiPower e b = 0))

/-- All incoming primitive coefficients equal the specified averaged four diagrams. -/
theorem primitive_checked : L24Symmetry.averageCoordinates
    (imageCoordinates destination coefficients) = primitiveClaim := by
  decide +kernel

/-- The complete candidate has exactly this primitive projection. -/
theorem full_primitive_checked :
    (fun i ↦ if primitive i then fullClaim i else 0) = primitiveClaim := by
  decide +kernel

/-- Exactly 721 full terms and 18 primitive terms have nonzero coefficients. -/
theorem support_sizes :
    (Finset.univ.filter fun i ↦ fullClaim i ≠ 0).card = 721 ∧
    (Finset.univ.filter fun i ↦ primitiveClaim i ≠ 0).card = 18 := by
  decide +kernel

/-- The retained genus-two components have total cotangent power at most one. -/
theorem no_high_genus_two_psi : ∀ i, fullClaim i ≠ 0 →
    ∀ v, (L24Graphs.graph i).graph.genus v = 2 →
      (∑ s : Fin 4, if (L24Graphs.graph i).graph.legVertex s = v then
        (L24Graphs.graph i).legPsiPower s else 0) +
      (∑ e, ∑ b : Fin 2, if (L24Graphs.graph i).graph.endpoint e b = v then
        (L24Graphs.graph i).halfEdgePsiPower e b else 0) ≤ 1 := by
  decide +kernel

/-- The primitive coordinate claim denotes the actual averaged paper diagrams. -/
theorem primitive_strata :
    L24Symmetry.average (interpret (fun i ↦ TautologicalStratum.mk (picture i)
      (picture_totalGenus i)) coefficients) = interpret L24Graphs.columns primitiveClaim := by
  let x : StrataOperation 2 (Fin 4) 2 (Fin 4) := .input
  have he := x.map_interpret picture picture_totalGenus L24Graphs.graph
    L24Graphs.graph_totalGenus coefficients destination (fun i _ ↦ pictures_covered i)
  change interpret (fun i ↦ TautologicalStratum.mk (picture i) (picture_totalGenus i))
    coefficients = interpret L24Graphs.columns (imageCoordinates destination coefficients) at he
  rw [he, L24Symmetry.average_interpret, primitive_checked]

end AxiomaticGW.L24Primitive
