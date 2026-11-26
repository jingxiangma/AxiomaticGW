/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates

/-!
# Finite common refinements of the held genus-two raw loop

This is a concrete finite graph computation, not a geometric product law.
A contraction retains one edge with ordered branches and contracts its entire
complement. Connectedness and the genus of that complement are checked.
Generic pairs cover every edge. Existing graph automorphisms act on both
contractions simultaneously; no target automorphism is divided out.

The graph representatives are the unchanged raw incidence fixtures. The final
finite classification uses the existing complete bounded graph enumerator.
No assertion about a boundary square or a cohomology realization is made.
-/

@[expose] public section
set_option autoImplicit false

-- Bound memory by checking the finite certificates sequentially.
set_option Elab.async false

namespace AxiomaticGW.GKM.LoopSquareRefinements

open AdmcyclesHodgeStrataCandidates
open scoped BigOperators

/-- The actual loop underlying rawGraph3. -/
def target : StableGraphCode (Fin 1) :=
  rawIncidence1Candidate.toGraph rawIncidence1Valid

/-- The held one-vertex two-loop incidence, underlying rawGraph12. -/
def doubleLoop : StableGraphCode (Fin 1) :=
  rawIncidence4Candidate.toGraph rawIncidence4Valid

/-- The held parallel-edge incidence, underlying rawGraph28. -/
def parallel : StableGraphCode (Fin 1) :=
  rawIncidence9Candidate.toGraph rawIncidence9Valid

/-- Every part of the held contraction target is explicit, including its old leg. -/
theorem target_shape :
    target.vertexCount = 1 ∧ target.edgeCount = 1 ∧ target.genus (0 : Fin 1) = 1 ∧
      target.legVertex 0 = (0 : Fin 1) ∧ (∀ e b, target.endpoint e b = (0 : Fin 1)) ∧
      Fintype.card (Fin 1) = 1 := by
  decide +kernel

/-- The decoded raw loop uses exactly the target incidence and zero powers. -/
theorem rawGraph3_incidence_and_powers :
    (DecoratedStableGraph.toDecoration rawIncidence1Candidate rawIncidence1Valid
      rawGraph3Exponents).graph = target ∧ rawGraph3Exponents = 0 := by
  exact ⟨rfl, by decide +kernel⟩

/-- The double-loop output uses its actual packet incidence and zero powers. -/
theorem rawGraph12_incidence_and_powers :
    (DecoratedStableGraph.toDecoration rawIncidence4Candidate rawIncidence4Valid
      rawGraph12Exponents).graph = doubleLoop ∧ rawGraph12Exponents = 0 := by
  exact ⟨rfl, by decide +kernel⟩

/-- The parallel output uses its actual packet incidence and zero powers. -/
theorem rawGraph28_incidence_and_powers :
    (DecoratedStableGraph.toDecoration rawIncidence9Candidate rawIncidence9Valid
      rawGraph28Exponents).graph = parallel ∧ rawGraph28Exponents = 0 := by
  exact ⟨rfl, by decide +kernel⟩

/-- Bind the quotient column itself to the decoded zero decoration. -/
theorem rawGraph3_zero_presentation :
    rawGraph3 = TautologicalStratum.mk
      (DecoratedStableGraph.toDecoration rawIncidence1Candidate rawIncidence1Valid
        (0 : DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ))
      (DecoratedStableGraph.toDecoration_totalGenus rawIncidence1Candidate
        rawIncidence1Valid (0 : DecoratedStableGraph.DecorationIndex (Fin 1) 1 1 4 → ℕ)) := by
  simp only [rawGraph3, rawGraph3_incidence_and_powers.2]

theorem rawGraph12_zero_presentation :
    rawGraph12 = TautologicalStratum.mk
      (DecoratedStableGraph.toDecoration rawIncidence4Candidate rawIncidence4Valid
        (0 : DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ))
      (DecoratedStableGraph.toDecoration_totalGenus rawIncidence4Candidate
        rawIncidence4Valid (0 : DecoratedStableGraph.DecorationIndex (Fin 1) 1 2 4 → ℕ)) := by
  simp only [rawGraph12, rawGraph12_incidence_and_powers.2]

theorem rawGraph28_zero_presentation :
    rawGraph28 = TautologicalStratum.mk
      (DecoratedStableGraph.toDecoration rawIncidence9Candidate rawIncidence9Valid
        (0 : DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ))
      (DecoratedStableGraph.toDecoration_totalGenus rawIncidence9Candidate
        rawIncidence9Valid (0 : DecoratedStableGraph.DecorationIndex (Fin 1) 2 2 4 → ℕ)) := by
  simp only [rawGraph28, rawGraph28_incidence_and_powers.2]

/-- An image edge and the image of target branch zero determine the injection. -/
abbrev ContractionCandidate (G : StableGraphCode (Fin 1)) :=
  Fin G.edgeCount × Fin 2

/-- The target has exactly one vertex, so its surjective vertex map is fixed. -/
def vertexMap (G : StableGraphCode (Fin 1)) : Fin G.vertexCount → Fin 1 :=
  fun _ ↦ 0

/-- Retain both ordered flags, including the branch-zero choice. -/
def flagMap {G : StableGraphCode (Fin 1)} (c : ContractionCandidate G)
    (b : Fin 2) : Fin G.edgeCount × Fin 2 :=
  (c.1, if b = 0 then c.2 else Equiv.swap 0 1 c.2)

/-- The constant vertex map is genuinely surjective because stable graphs are nonempty. -/
theorem vertexMap_surjective (G : StableGraphCode (Fin 1)) :
    Function.Surjective (vertexMap G) := by
  intro v
  exact ⟨⟨0, G.vertexCount_pos⟩, Subsingleton.elim _ _⟩

/-- The old marking retains its label and its image vertex. -/
theorem leg_compatibility (G : StableGraphCode (Fin 1)) (s : Fin 1) :
    vertexMap G (G.legVertex s) = target.legVertex s :=
  Subsingleton.elim _ _

/-- The flag formula is a permutation of the two branches on its retained edge. -/
theorem flagMap_branch {G : StableGraphCode (Fin 1)} (c : ContractionCandidate G)
    (b : Fin 2) :
    (flagMap c b).2 =
      (if c.2 = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1) b := by
  rcases c with ⟨e, i⟩
  fin_cases i <;> fin_cases b <;> rfl

/-- No two target flags are identified. -/
theorem flagMap_injective {G : StableGraphCode (Fin 1)} (c : ContractionCandidate G) :
    Function.Injective (flagMap c) := by
  intro a b h
  have hbranch := congrArg Prod.snd h
  rw [flagMap_branch, flagMap_branch] at hbranch
  exact (if c.2 = 0 then Equiv.refl (Fin 2) else Equiv.swap 0 1).injective hbranch

/-- The injection commutes with the involution pairing the two edge branches. -/
theorem flagMap_mate {G : StableGraphCode (Fin 1)} (c : ContractionCandidate G)
    (b : Fin 2) :
    flagMap c (Equiv.swap 0 1 b) =
      ((flagMap c b).1, Equiv.swap 0 1 (flagMap c b).2) := by
  rcases c with ⟨e, i⟩
  fin_cases i <;> fin_cases b <;> rfl

/-- Both injected flags belong to precisely the retained source edge. -/
theorem flagMap_edge {G : StableGraphCode (Fin 1)} (c : ContractionCandidate G)
    (b : Fin 2) : (flagMap c b).1 = c.1 := rfl

/-- Incidence commutes with the actual vertex map and fixed target loop. -/
theorem endpoint_compatibility {G : StableGraphCode (Fin 1)}
    (c : ContractionCandidate G) (b : Fin 2) :
    vertexMap G (G.endpoint (flagMap c b).1 (flagMap c b).2) = target.endpoint (0 : Fin 1) b :=
  Subsingleton.elim _ _

/-- The complement really has one fewer edge, including when the retained edge is a loop. -/
theorem contracted_edge_count (G : StableGraphCode (Fin 1)) (c : ContractionCandidate G) :
    ((Finset.univ : Finset (Fin G.edgeCount)).erase c.1).card = G.edgeCount - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- Incidence in the whole contracted complement, with all vertices retained. -/
def contractedIncidence (G : StableGraphCode (Fin 1)) (kept : Fin G.edgeCount) :
    SimpleGraph (Fin G.vertexCount) :=
  SimpleGraph.fromRel (fun x y ↦ ∃ e : Fin G.edgeCount, e ≠ kept ∧
    ((G.endpoint e 0 = x ∧ G.endpoint e 1 = y) ∨
      (G.endpoint e 1 = x ∧ G.endpoint e 0 = y)))

instance (G : StableGraphCode (Fin 1)) (kept : Fin G.edgeCount) :
    DecidableRel (contractedIncidence G kept).Adj := by
  unfold contractedIncidence
  infer_instance

/-- The actual connected fibre contracts to genus one. Loops in the complement
contribute their first Betti number; genus is never merely summed over vertices. -/
def Contracts (G : StableGraphCode (Fin 1)) (c : ContractionCandidate G) : Prop :=
  (contractedIncidence G c.1).Connected ∧
    (∑ v, G.genus v) + (G.edgeCount - 1 + 1 - G.vertexCount) = target.genus (0 : Fin 1)

instance (G : StableGraphCode (Fin 1)) (c : ContractionCandidate G) :
    Decidable (Contracts G c) := by
  unfold Contracts
  infer_instance

/-- The checked genus equals the arithmetic genus of the single contracted
fibre, using its actual edge count instead of an unrelated supplied number. -/
theorem contracted_fibre_genus (G : StableGraphCode (Fin 1))
    (c : ContractionCandidate G) (hc : Contracts G c) :
    (∑ v, G.genus v) +
      (((Finset.univ : Finset (Fin G.edgeCount)).erase c.1).card + 1 - G.vertexCount) =
        target.genus (0 : Fin 1) := by
  rw [contracted_edge_count]
  exact hc.2

abbrev PairCandidate (G : StableGraphCode (Fin 1)) :=
  ContractionCandidate G × ContractionCandidate G

/-- Both maps contract to the held target, and their retained edges cover G. -/
def Generic (G : StableGraphCode (Fin 1)) (p : PairCandidate G) : Prop :=
  Contracts G p.1 ∧ Contracts G p.2 ∧ ∀ e, e = p.1.1 ∨ e = p.2.1

instance (G : StableGraphCode (Fin 1)) (p : PairCandidate G) :
    Decidable (Generic G p) := by
  unfold Generic
  infer_instance

/-- Exhaustively enumerate the two contraction maps with ordered flags. -/
def pairs (G : StableGraphCode (Fin 1)) : Finset (PairCandidate G) :=
  Finset.univ.filter (Generic G)

theorem mem_pairs_iff (G : StableGraphCode (Fin 1)) (p : PairCandidate G) :
    p ∈ pairs G ↔ Generic G p := by
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Genericity supplies a two-element cover, so no third edge is admissible. -/
theorem edgeCount_le_two (G : StableGraphCode (Fin 1)) (p : PairCandidate G)
    (hp : Generic G p) : G.edgeCount ≤ 2 := by
  let f : Fin 2 → Fin G.edgeCount := ![p.1.1, p.2.1]
  have hf : Function.Surjective f := by
    intro e
    rcases hp.2.2 e with he | he
    · exact ⟨0, he.symm⟩
    · exact ⟨1, he.symm⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f hf

/-- Connectedness supplies the only further size bound used in the finite search. -/
theorem vertexCount_le_three (G : StableGraphCode (Fin 1)) (p : PairCandidate G)
    (hp : Generic G p) : G.vertexCount ≤ 3 := by
  have he := edgeCount_le_two G p hp
  have hv := G.vertexCount_le_edgeCount_add_one
  omega

/-- Act on the retained edge and the image of branch zero using the existing
complete isomorphism candidates. -/
def actContraction {G : StableGraphCode (Fin 1)}
    (a : StableGraphCode.IsoCandidate G G) (c : ContractionCandidate G) :
    ContractionCandidate G :=
  (a.2.1 c.1, a.2.2 c.1 c.2)

def actPair {G : StableGraphCode (Fin 1)} (a : StableGraphCode.IsoCandidate G G)
    (p : PairCandidate G) : PairCandidate G :=
  (actContraction a p.1, actContraction a p.2)

/-- Simultaneous source-graph automorphisms; left/right targets stay fixed. -/
def orbit (G : StableGraphCode (Fin 1)) (p : PairCandidate G) :
    Finset (PairCandidate G) :=
  (StableGraphCode.isoCandidates G G).image (fun a ↦ actPair a p)

/-- Equal finite orbits are merged. This does not merge ordered target flags. -/
def orbits (G : StableGraphCode (Fin 1)) : Finset (Finset (PairCandidate G)) :=
  (pairs G).image (orbit G)

/-- Verify both ordered flags, not only the stored image of branch zero. -/
def FlagActionCorrect (G : StableGraphCode (Fin 1)) : Prop :=
  ∀ a ∈ StableGraphCode.isoCandidates G G, ∀ c : ContractionCandidate G, ∀ b,
    flagMap (actContraction a c) b =
      (a.2.1 (flagMap c b).1, a.2.2 (flagMap c b).1 (flagMap c b).2)

instance (G : StableGraphCode (Fin 1)) : Decidable (FlagActionCorrect G) := by
  unfold FlagActionCorrect
  infer_instance

/-- On the held representatives the computed sets really partition the accepted
pairs into complete simultaneous-automorphism orbits. -/
def OrbitPartition (G : StableGraphCode (Fin 1)) : Prop :=
  ∀ p ∈ pairs G, p ∈ orbit G p ∧ orbit G p ⊆ pairs G ∧
    ∀ q ∈ pairs G, q ∈ orbit G p ↔ orbit G q = orbit G p

instance (G : StableGraphCode (Fin 1)) : Decidable (OrbitPartition G) := by
  letI : DecidableEq (PairCandidate G) := inferInstance
  unfold OrbitPartition
  infer_instance

theorem actual_flag_actions :
    FlagActionCorrect target ∧ FlagActionCorrect doubleLoop ∧
      FlagActionCorrect parallel := by
  decide +kernel

theorem actual_orbit_partitions :
    OrbitPartition target ∧ OrbitPartition doubleLoop ∧ OrbitPartition parallel := by
  decide +kernel

/-- Actual counts before and after graph automorphisms for the shared edge. -/
theorem shared_counts :
    (pairs target).card = 4 ∧ target.automorphismCount = 2 ∧
      (orbits target).card = 2 := by
  decide +kernel

/-- Two distinct retained loop edges give one orbit, not an extra factor 1/8. -/
theorem doubleLoop_counts :
    (pairs doubleLoop).card = 8 ∧ doubleLoop.automorphismCount = 8 ∧
      (orbits doubleLoop).card = 1 := by
  decide +kernel

/-- The four relative ordered-flag choices survive for the parallel graph. -/
theorem parallel_counts :
    (pairs parallel).card = 8 ∧ parallel.automorphismCount = 2 ∧
      (orbits parallel).card = 4 := by
  decide +kernel

/-- Stabilizers are checked for these three graphs rather than postulated. -/
def FreeOnPairs (G : StableGraphCode (Fin 1)) : Prop :=
  ∀ p ∈ pairs G, ∀ a ∈ StableGraphCode.isoCandidates G G,
    actPair a p = p → a = (StableGraphCode.Iso.refl G).toCandidate

instance (G : StableGraphCode (Fin 1)) : Decidable (FreeOnPairs G) := by
  letI : DecidableEq (PairCandidate G) := inferInstance
  letI : DecidableEq (StableGraphCode.IsoCandidate G G) := inferInstance
  unfold FreeOnPairs
  infer_instance

theorem actual_stabilizers_trivial :
    FreeOnPairs target ∧ FreeOnPairs doubleLoop ∧ FreeOnPairs parallel := by
  decide +kernel

/-- Every stable candidate with a generic pair is one of the three graph types.
This test retains the existing graph-isomorphism semantics. -/
def classificationTest {v e : ℕ} (c : StableGraphCode.Candidate (Fin 1) v e) : Bool :=
  if h : c.Valid 2 then
    let G := c.toGraph h
    if (pairs G).Nonempty then
      G.isomorphic? target || G.isomorphic? doubleLoop || G.isomorphic? parallel
    else true
  else false

/-- Check the entire existing finite graph enumeration, not a supplied graph list. -/
def classificationCheck (v e : ℕ) : Bool :=
  decide (∀ c ∈ StableGraphCode.candidates (Fin 1) 2 v e, classificationTest c = true)

end AxiomaticGW.GKM.LoopSquareRefinements
