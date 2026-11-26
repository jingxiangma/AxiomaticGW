/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.SurfaceLocalizationVertex
public import AxiomaticGW.GKM.Fixtures.SurfaceEdgeReplay
public import AxiomaticGW.GKM.Fixtures.StrictLineGeometricLocus

/-! # Reading all three source-curve vertices from the doubled strict-line graph -/

@[expose] public noncomputable section
namespace AxiomaticGW.GKM.StrictLineDoubleCoverChain
open SurfaceLocalizationVertex EquivariantCoefficients
open StrictLineCoverTransport (line_characters)
open StrictLineVertexTransport (branches)
open ExceptionalGenusTwoVertexValues (seed)
open CurveReplay.TwoBlowups renaming tables → bl2

/-- The two incoming center flags have different source-edge labels. -/
theorem incident_flags :
    flagsAt graph 0 = [(0,0)] ∧ flagsAt graph 1 = [(0,1), (1,1)] ∧
    flagsAt graph 2 = [(1,0)] := by decide +kernel

/-- The indexed half-edges acquire opposite characters at the two ends of each cover. -/
theorem outgoing_weights (j : Fin 2) :
    outgoing graph (j,0) = x ∧ outgoing graph (j,1) = -x := by
  have first : graph.image (graph.endpoint j 0) = (bl2.edges 3).source :=
    (by decide +kernel : ∀ s, graph.image (graph.endpoint s 0) = (bl2.edges 3).source) j
  have edge : graph.edgeIndex j = 3 := rfl
  have sheets : (graph.cover j).val = 1 := rfl
  have weight : outgoing graph (j,0) = x := by
    simp only [outgoing, edge, first, if_pos, sheets, Nat.cast_one, div_one, line_characters.1]
  exact ⟨weight, (outgoing_opposite CurveReplay.TwoBlowups.accepted graph j).trans
    (congrArg Neg.neg weight)⟩

/-- The actual marking goes to the genus-two center. The remaining source vertices use the
unmarked, one-edge rational convention. -/
theorem source_vertices (p : Fin 3) :
    atVertex? graph ![0,2,0] (fun _ : Fin 1 ↦ 1) (fun _ ↦ 3) p seed =
      some (![x / (x*(y-x)), ExceptionalDoubleCoverChain.center [3] (-x) y, x / (x*(y-x))] p) := by
  classical
  have leafFactor : factor? seed 0 []
      (CurveConventionCertificate.character (bl2.tangent (bl2.edges 3).source 0))
      (CurveConventionCertificate.character (bl2.tangent (bl2.edges 3).source 1)) [x] =
      some (x / (x*(y-x))) := by
    rw [branches.1, branches.2.1, factor?, if_neg]
    simp only [List.mem_singleton, x_ne_zero, y_sub_x_ne_zero, Ne.symm x_ne_zero,
      or_self, not_false_eq_true]
  have centerFactor : factor? seed 2 [3]
      (CurveConventionCertificate.character (bl2.tangent (bl2.edges 3).target 0))
      (CurveConventionCertificate.character (bl2.tangent (bl2.edges 3).target 1)) [-x,-x] =
      some (ExceptionalDoubleCoverChain.center [3] (-x) y) := by
    have hx := neg_ne_zero.mpr x_ne_zero
    rw [branches.2.2.1, branches.2.2.2, factor?, if_neg]
    · change some (GenusTwoLocalizationVertex.reduced seed [3] y (-x) [-x,-x].get) = _
      have two : [-x,-x].get = fun _ ↦ -x := by funext s; fin_cases s <;> rfl
      rw [two, GenusTwoLocalizationVertex.reduced, GenusTwoLocalizationVertex.swap]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, y_ne_zero, hx, Ne.symm hx, or_self,
        not_false_eq_true]
  have marks : ∀ i : Fin 3, powersAt (fun _ : Fin 1 ↦ (1 : Fin 3)) (fun _ ↦ 3) i =
      (![[], [3], []] i) := by decide +kernel
  rcases (by decide +kernel : ∀ q : Fin 3, q = 0 ∨ q = 1 ∨ q = 2) p with rfl | rfl | rfl
  · simp only [atVertex?, incident_flags.1, marks, List.map_cons, List.map_nil,
      (outgoing_weights 0).1]
    exact leafFactor
  · simp only [atVertex?, incident_flags.2.1, marks, List.map_cons, List.map_nil,
      (outgoing_weights 0).2, (outgoing_weights 1).2]
    exact centerFactor
  · simp only [atVertex?, incident_flags.2.2, marks, List.map_cons, List.map_nil,
      (outgoing_weights 1).1]
    exact leafFactor

/-- The general surface edge rule specializes to the exceptional normal bundle on both covers. -/
theorem edge_factors (j : Fin 2) :
    SurfaceLocalizationEdge.atEdge? bl2 (graph.edgeIndex j) (graph.cover j) =
      some (ExceptionalCoverFactors.atEdge bl2 (graph.edgeIndex j) (graph.cover j)) := by
  apply SurfaceEdgeReplay.negative_one
  · rfl
  · change CurveConventionCertificate.character (bl2.edges 3).weight ≠ 0
    rw [line_characters.1]
    exact x_ne_zero

/-- Read all three source factors from the indexed graph before applying its edge, tangent,
insertion and automorphism factors. Any unsupported source vertex propagates a missing value. -/
def graphContribution? : Option Coefficient := do
  let vertices ← (List.finRange 3).mapM fun p ↦
    atVertex? graph ![0,2,0] (fun _ : Fin 1 ↦ 1) (fun _ ↦ 3) p seed
  let edges ← (List.finRange 2).mapM fun e ↦
    SurfaceLocalizationEdge.atEdge? bl2 (graph.edgeIndex e) (graph.cover e)
  return edges.prod *
    (∏ w, ExceptionalCoverFactors.tangent bl2 (graph.image w) (valence w)) *
    SurfaceFrames.TwoBlowups.request.restrictions (graph.image 1) 3 *
    vertices.prod / ExceptionalDoubleCoverChain.symmetries.card

/-- The support, marked vertex, oriented flags, unstable leaves and their exchange
recover the complete signed rational function before ordinary specialization. -/
theorem graph_contribution : graphContribution? = some (rationalExpression x y) := by
  have vertices := source_vertices
  unfold graphContribution?
  rw [show List.finRange 3 = [0,1,2] by decide +kernel]
  rw [show List.finRange 2 = [0,1] by decide +kernel]
  simp only [List.mapM_cons, List.mapM_nil, vertices, edge_factors]
  change some (_ * _ * _ * ((x / (x*(y-x))) *
    (ExceptionalDoubleCoverChain.center [3] (-x) y * (x / (x*(y-x)) * 1))) / _) = _
  rw [mul_one, ← mul_assoc (x / (x*(y-x)))]
  apply congrArg some
  have h := locus_value
  have covers : graph.cover = fun _ ↦ 1 := rfl
  rw [locus, withCenter, covers, bivalent, leaf] at h
  rw [Fin.prod_univ_two] at h
  simpa only [covers, List.prod_cons, List.prod_nil, mul_one] using h

end AxiomaticGW.GKM.StrictLineDoubleCoverChain
