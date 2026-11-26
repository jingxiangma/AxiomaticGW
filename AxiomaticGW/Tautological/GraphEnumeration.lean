/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphBounds
public import AxiomaticGW.Tautological.GraphIsomorphisms
public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Bounded enumeration of decorated strata

Raw finite incidence and exponent data are checked against the existing stable
and decorated graph syntax. Kappa indices start at one. Fixed external labels,
loop branches, and repeated edges remain distinct until the existing graph
isomorphism relation identifies presentations. Degree-bounded exponent search
uses antidiagonal tuples rather than a full exponent box.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace TautologicalStratum

/-- Equality of stratum classes is decidable by the finite decorated-graph
isomorphism enumeration. -/
instance {g : ℕ} {S : Type} [Fintype S] : DecidableEq (TautologicalStratum g S) := by
  letI : DecidableRel (decoratedStratumSetoid g S).r := fun G H ↦
    decidable_of_iff (DecoratedStableGraph.isomorphic? G.1 H.1 = true)
      (DecoratedStableGraph.isomorphic?_eq_true_iff G.1 H.1)
  exact Quotient.decidableEq

end TautologicalStratum

namespace StableGraphCode

/-- Raw fixed-size incidence data. A candidate becomes a stable graph only
after its connectedness, stability, and arithmetic genus are checked. -/
structure Candidate (S : Type) [Fintype S] (v e : ℕ) where
  /-- External leg incidence. -/
  legVertex : S → Fin v
  /-- Two independently labelled branches per edge. -/
  endpoint : Fin e → Fin 2 → Fin v
  /-- Nonnegative vertex genera. -/
  genus : Fin v → ℕ

/-- Fixed-size raw graph equality compares just the finite incidence and
genus functions, with no additional equality assumption on external labels. -/
instance {S : Type} [Fintype S] {v e : ℕ} : DecidableEq (Candidate S v e) :=
  fun c d ↦ decidable_of_iff
    (c.legVertex = d.legVertex ∧ c.endpoint = d.endpoint ∧ c.genus = d.genus) (by
      cases c
      cases d
      simp only [Candidate.mk.injEq])

namespace Candidate

variable {S : Type} [Fintype S] {v e : ℕ}

/-- Vertex stability in the raw data, counting loops twice. -/
def Stable (c : Candidate S v e) : Prop := ∀ vertex,
  3 ≤ 2 * c.genus vertex +
    Fintype.card {s : S // c.legVertex s = vertex} +
    Fintype.card {p : Fin e × Fin 2 // c.endpoint p.1 p.2 = vertex}

instance (c : Candidate S v e) : Decidable c.Stable :=
  inferInstanceAs (Decidable (∀ _vertex, (_ : ℕ) ≤ (_ : ℕ)))

/-- The complete finite check needed to interpret a candidate at genus `g`. -/
def Valid (c : Candidate S v e) (g : ℕ) : Prop :=
  0 < v ∧ (incidenceGraph c.endpoint).Connected ∧ c.Stable ∧
    (∑ vertex, c.genus vertex) + (e + 1 - v) = g

instance (c : Candidate S v e) (g : ℕ) : Decidable (c.Valid g) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop) ∧ (_ : Prop)))

/-- Interpret checked raw incidence data in the existing graph syntax. -/
def toGraph (c : Candidate S v e) {g : ℕ} (h : c.Valid g) : StableGraphCode S where
  vertexCount := v
  edgeCount := e
  vertexCount_pos := h.1
  legVertex := c.legVertex
  endpoint := c.endpoint
  genus := c.genus
  connected := fun x y ↦ (reachable_iff c.endpoint x y).1 (h.2.1.preconnected x y)
  stable := h.2.2.1

/-- The graph decoded from a valid candidate has the requested genus. -/
theorem toGraph_totalGenus (c : Candidate S v e) {g : ℕ} (h : c.Valid g) :
    (c.toGraph h).totalGenus = g := h.2.2.2

/-- Forget the validity proofs of an existing graph. -/
def ofGraph (G : StableGraphCode S) : Candidate S G.vertexCount G.edgeCount where
  legVertex := G.legVertex
  endpoint := G.endpoint
  genus := G.genus

/-- Existing graphs pass the same finite validity check used by enumeration. -/
theorem ofGraph_valid (G : StableGraphCode S) {g : ℕ} (hg : G.totalGenus = g) :
    (ofGraph G).Valid g :=
  ⟨G.vertexCount_pos, incidenceGraph_connected G, G.stable, hg⟩

/-- Encoding and decoding preserve the whole graph presentation. -/
theorem toGraph_ofGraph (G : StableGraphCode S) {g : ℕ} (hg : G.totalGenus = g) :
    (ofGraph G).toGraph (ofGraph_valid G hg) = G := rfl

end Candidate

/-- A leg incidence map with its exact, materialized fibre cardinalities.
The compatibility field excludes incoherent cached counts. -/
structure CountedLegAssignment (S : Type) [Fintype S] (v : ℕ) where
  /-- Incidence of each fixed external label. -/
  legVertex : S → Fin v
  /-- Number of external legs on each vertex. -/
  counts : Vector ℕ v
  /-- Every cached entry equals its actual incidence fibre cardinality. -/
  counts_eq : ∀ vertex : Fin v,
    counts[vertex.1] = Fintype.card {s : S // legVertex s = vertex}

namespace CountedLegAssignment

/-- The incidence map determines the cached assignment. -/
theorem ext {S : Type} [Fintype S] {v : ℕ}
    {a b : CountedLegAssignment S v} (h : a.legVertex = b.legVertex) : a = b := by
  cases a with
  | mk legs counts hcounts =>
    cases b with
    | mk legs' counts' hcounts' =>
      dsimp only at h
      subst legs'
      have hc : counts = counts' := by
        apply Vector.ext
        intro i hi
        exact (hcounts ⟨i, hi⟩).trans (hcounts' ⟨i, hi⟩).symm
      subst counts'
      rfl

/-- Materialize the fibre counts of an arbitrary leg map. -/
def ofLegVertex {S : Type} [Fintype S] {v : ℕ}
    (legs : S → Fin v) : CountedLegAssignment S v where
  legVertex := legs
  counts := Vector.ofFn (fun vertex ↦ Fintype.card {s : S // legs s = vertex})
  counts_eq vertex := by simp only [Vector.getElem_ofFn, Fin.eta]

/-- The cached leg counts meet each vertex requirement. -/
def Meets {S : Type} [Fintype S] {v : ℕ}
    (a : CountedLegAssignment S v) (required : Vector ℕ v) : Prop :=
  ∀ vertex : Fin v, required[vertex.1] ≤ a.counts[vertex.1]

instance {S : Type} [Fintype S] {v : ℕ}
    (a : CountedLegAssignment S v) (required : Vector ℕ v) : Decidable (a.Meets required) :=
  inferInstanceAs (Decidable (∀ _vertex : Fin v, (_ : ℕ) ≤ (_ : ℕ)))

end CountedLegAssignment

/-- Minimum external leg count imposed by vertex stability. Internal
branches, including both sides of loops, are counted before leg search. -/
def requiredLegs {v e : ℕ} (endpoint : Fin e → Fin 2 → Fin v)
    (genus : Fin v → ℕ) : Vector ℕ v :=
  Vector.ofFn (fun vertex ↦ 3 - (2 * genus vertex +
    Fintype.card {p : Fin e × Fin 2 // endpoint p.1 p.2 = vertex}))

/-- Cached counts and minimum requirements express the original stability
condition exactly, including vertices whose requirement is zero. -/
theorem meets_requiredLegs_iff {S : Type} [Fintype S] {v e : ℕ}
    (legs : CountedLegAssignment S v) (endpoint : Fin e → Fin 2 → Fin v)
    (genus : Fin v → ℕ) :
    legs.Meets (requiredLegs endpoint genus) ↔
      (Candidate.mk legs.legVertex endpoint genus).Stable := by
  simp only [CountedLegAssignment.Meets, requiredLegs, Vector.getElem_ofFn,
    Fin.eta, legs.counts_eq, Candidate.Stable]
  apply forall_congr'
  intro vertex
  omega

/-- All labelled leg assignments, materializing each count vector once. -/
def countedLegAssignments (S : Type) [Fintype S] [DecidableEq S] (v : ℕ) :
    Finset (CountedLegAssignment S v) :=
  (Finset.univ : Finset (S → Fin v)).map
    ⟨CountedLegAssignment.ofLegVertex,
      fun _ _ h ↦ congrArg CountedLegAssignment.legVertex h⟩

/-- Every coherent counted assignment appears in the finite leg search. -/
theorem mem_countedLegAssignments {S : Type} [Fintype S] [DecidableEq S] {v : ℕ}
    (a : CountedLegAssignment S v) : a ∈ countedLegAssignments S v := by
  apply Finset.mem_map.mpr
  exact ⟨a.legVertex, Finset.mem_univ _, CountedLegAssignment.ext rfl⟩


variable (S : Type) [Fintype S] [DecidableEq S]

/-- Genus assignments with the required sum and graph first Betti number. -/
def genusAssignments (g v e : ℕ) : Finset (Fin v → ℕ) :=
  if e + 1 - v ≤ g then Finset.Nat.antidiagonalTuple v (g - (e + 1 - v)) else ∅

theorem mem_genusAssignments (g v e : ℕ) (a : Fin v → ℕ) :
    a ∈ genusAssignments g v e ↔ (∑ i, a i) + (e + 1 - v) = g := by
  unfold genusAssignments
  split_ifs with h
  · rw [Finset.Nat.mem_antidiagonalTuple]
    omega
  · simp only [Finset.notMem_empty, false_iff]
    omega

/-- Reject vertex counts forbidden by summed stability, then enumerate
connected incidence, genus assignments, and stable leg distributions.
Injective construction and disjoint genus/incidence groups avoid duplicate
comparisons between distinct raw presentations. -/
def candidates (g v e : ℕ) : Finset (Candidate S v e) :=
  if v + 2 ≤ 2 * g + Fintype.card S then
    let legData := countedLegAssignments S v
    ((Finset.univ : Finset (Fin e → Fin 2 → Fin v)).filter
      (fun endpoint ↦ 0 < v ∧ (incidenceGraph endpoint).Connected)).disjiUnion
        (fun endpoint ↦ (genusAssignments g v e).disjiUnion
          (fun genus ↦
            let required := requiredLegs endpoint genus
            (legData.filter (fun legs ↦ legs.Meets required)).map
              ⟨fun legs ↦ Candidate.mk legs.legVertex endpoint genus,
                fun _ _ h ↦ CountedLegAssignment.ext (congrArg Candidate.legVertex h)⟩)
          (by
            intro genus _ genus' _ hne
            apply Finset.disjoint_left.mpr
            intro c hc hc'
            rcases Finset.mem_map.mp hc with ⟨legs, _, rfl⟩
            rcases Finset.mem_map.mp hc' with ⟨legs', _, heq⟩
            exact hne (congrArg Candidate.genus heq).symm))
        (by
          intro endpoint _ endpoint' _ hne
          apply Finset.disjoint_left.mpr
          intro c hc hc'
          rcases Finset.mem_disjiUnion.mp hc with ⟨genus, _, hc⟩
          rcases Finset.mem_disjiUnion.mp hc' with ⟨genus', _, hc'⟩
          rcases Finset.mem_map.mp hc with ⟨legs, _, rfl⟩
          rcases Finset.mem_map.mp hc' with ⟨legs', _, heq⟩
          exact hne (congrArg Candidate.endpoint heq).symm)
  else ∅

/-- Incidence enumeration is sound and complete for raw fixed-size graphs. -/
theorem mem_candidates (g v e : ℕ) (c : Candidate S v e) :
    c ∈ candidates S g v e ↔ c.Valid g := by
  unfold candidates
  split_ifs with hsize
  · simp only [Finset.mem_disjiUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_map, Function.Embedding.coeFn_mk, mem_genusAssignments,
      mem_countedLegAssignments, meets_requiredLegs_iff]
    constructor
    · rintro ⟨endpoint, hp, genus, hg, legs, hs, heq⟩
      subst c
      exact ⟨hp.1, hp.2, hs, hg⟩
    · intro h
      exact ⟨c.endpoint, ⟨h.1, h.2.1⟩, c.genus, h.2.2.2,
        CountedLegAssignment.ofLegVertex c.legVertex, h.2.2.1, rfl⟩
  · simp only [Finset.notMem_empty, false_iff]
    intro hc
    apply hsize
    have h := (c.toGraph hc).vertexCount_add_two_le
    rw [Candidate.toGraph_totalGenus] at h
    exact h

/-- Direct finite incidence search used as the reference presentation for
kernel evaluation. The optimized candidate search is proved equal to it. -/
def standardCandidates (g v e : ℕ) : Finset (Candidate S v e) :=
  ((Finset.univ : Finset (Fin e → Fin 2 → Fin v)).filter
    (fun endpoint ↦ 0 < v ∧ (incidenceGraph endpoint).Connected)).disjiUnion
      (fun endpoint ↦ (genusAssignments g v e).disjiUnion
        (fun genus ↦ ((Finset.univ : Finset (S → Fin v)).filter
          (fun legs ↦ (Candidate.mk legs endpoint genus).Stable)).map
            ⟨fun legs ↦ Candidate.mk legs endpoint genus,
              fun _ _ h ↦ congrArg Candidate.legVertex h⟩)
        (by
          intro genus _ genus' _ hne
          apply Finset.disjoint_left.mpr
          intro c hc hc'
          rcases Finset.mem_map.mp hc with ⟨legs, _, rfl⟩
          rcases Finset.mem_map.mp hc' with ⟨legs', _, heq⟩
          exact hne (congrArg Candidate.genus heq).symm))
      (by
        intro endpoint _ endpoint' _ hne
        apply Finset.disjoint_left.mpr
        intro c hc hc'
        rcases Finset.mem_disjiUnion.mp hc with ⟨genus, _, hc⟩
        rcases Finset.mem_disjiUnion.mp hc' with ⟨genus', _, hc'⟩
        rcases Finset.mem_map.mp hc with ⟨legs, _, rfl⟩
        rcases Finset.mem_map.mp hc' with ⟨legs', _, heq⟩
        exact hne (congrArg Candidate.endpoint heq).symm)

/-- Count materialization and stability pruning preserve the standard raw
incidence search. This form supports kernel evaluation of small fixtures. -/
theorem candidates_eq_standard (g v e : ℕ) :
    candidates S g v e = standardCandidates S g v e := by
  unfold standardCandidates
  ext c
  rw [mem_candidates]
  simp only [Finset.mem_disjiUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map, Function.Embedding.coeFn_mk, mem_genusAssignments]
  constructor
  · intro h
    exact ⟨c.endpoint, ⟨h.1, h.2.1⟩, c.genus, h.2.2.2,
      c.legVertex, h.2.2.1, rfl⟩
  · rintro ⟨endpoint, hp, genus, hg, legs, hs, heq⟩
    subst c
    exact ⟨hp.1, hp.2, hs, hg⟩

/-- Reference candidates have exactly the original graph-validity meaning. -/
theorem mem_standardCandidates (g v e : ℕ) (c : Candidate S v e) :
    c ∈ standardCandidates S g v e ↔ c.Valid g := by
  rw [← candidates_eq_standard]
  exact mem_candidates S g v e c

/-- Package validity in a fixed subtype, independent of the implementation
of the finite search. This permits reference-search rewrites under graph
interpretation without transporting a membership-indexed type. -/
def validCandidates (g v e : ℕ) : Finset {c : Candidate S v e // c.Valid g} :=
  (candidates S g v e).attach.map
    ⟨fun c : {c : Candidate S v e // c ∈ candidates S g v e} ↦
        ⟨c.1, (mem_candidates S g v e c.1).1 c.2⟩,
      fun _ _ h ↦ Subtype.ext
        (congrArg (fun z : {c : Candidate S v e // c.Valid g} ↦ z.1) h)⟩

/-- Every valid fixed-size graph occurs in the proof-facing search. -/
theorem mem_validCandidates (g v e : ℕ) (c : {c : Candidate S v e // c.Valid g}) :
    c ∈ validCandidates S g v e := by
  rw [validCandidates]
  apply Finset.mem_map.mpr
  exact ⟨⟨c.1, (mem_candidates S g v e c.1).2 c.2⟩, Finset.mem_attach _ _, rfl⟩

/-- Validity-indexed candidates admit a reducible reference search. -/
theorem validCandidates_eq_standard (g v e : ℕ) :
    validCandidates S g v e =
      (standardCandidates S g v e).attach.map
        ⟨fun c : {c : Candidate S v e // c ∈ standardCandidates S g v e} ↦
            ⟨c.1, (mem_standardCandidates S g v e c.1).1 c.2⟩,
          fun _ _ h ↦ Subtype.ext
            (congrArg (fun z : {c : Candidate S v e // c.Valid g} ↦ z.1) h)⟩ := by
  ext c
  apply iff_of_true (mem_validCandidates S g v e c)
  apply Finset.mem_map.mpr
  exact ⟨⟨c.1, (mem_standardCandidates S g v e c.1).2 c.2⟩,
    Finset.mem_attach _ _, rfl⟩

end StableGraphCode

namespace DecoratedStableGraph

/-- Finite coordinates for all decorations at a fixed bound. The first
summand indexes kappa powers and the other summands index psi powers. -/
abbrev DecorationIndex (S : Type) (v e d : ℕ) :=
  (Fin v × Fin d) ⊕ (S ⊕ (Fin e × Fin 2))

/-- Codimension weight of a decoration coordinate. -/
def decorationWeight {S : Type} {v e d : ℕ} : DecorationIndex S v e d → ℕ
  | .inl (_, i) => i.1 + 1
  | .inr _ => 1

theorem decorationWeight_pos {S : Type} {v e d : ℕ} (i : DecorationIndex S v e d) :
    0 < decorationWeight i := by
  cases i <;> exact Nat.succ_pos _

/-- Explicit dense indices for kappa, external psi, and internal psi
coordinates. Only the chosen enumeration of external labels is auxiliary;
incidence and decoration data retain their original labels. -/
def decorationCoordinateEquiv {S : Type} [Fintype S]
    (labels : S ≃ Fin (Fintype.card S)) (v e d : ℕ) :
    DecorationIndex S v e d ≃ Fin (v * d + (Fintype.card S + e * 2)) :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr labels finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

/-- Dense exponent functions are equivalent to array-backed vectors. -/
def exponentTupleEquiv (n : ℕ) : (Fin n → ℕ) ≃ Vector ℕ n where
  toFun := Vector.ofFn
  invFun a i := a[i.1]
  left_inv a := by
    funext i
    simp only [Vector.getElem_ofFn]
  right_inv a := Vector.ofFn_getElem

/-- Materialize the exponent tuples as vectors before transporting their
lookup functions along explicit coordinate indices. The intermediate vector
map keeps array construction outside repeated exponent lookup. -/
def decorationTuplesOfLabels {S : Type} [Fintype S]
    (labels : S ≃ Fin (Fintype.card S)) (v e d total : ℕ) :
    Finset (DecorationIndex S v e d → ℕ) :=
  ((Finset.Nat.antidiagonalTuple (v * d + (Fintype.card S + e * 2)) total).map
    (exponentTupleEquiv _).toEmbedding).map
      ((exponentTupleEquiv _).symm.trans
        ((decorationCoordinateEquiv labels v e d).symm.arrowCongr (Equiv.refl ℕ))).toEmbedding

/-- Explicit coordinate transport preserves the full sum constraint. -/
theorem mem_decorationTuplesOfLabels {S : Type} [Fintype S]
    (labels : S ≃ Fin (Fintype.card S)) (v e d total : ℕ)
    (a : DecorationIndex S v e d → ℕ) :
    a ∈ decorationTuplesOfLabels labels v e d total ↔ ∑ i, a i = total := by
  let q := decorationCoordinateEquiv labels v e d
  have hmap : (exponentTupleEquiv _).toEmbedding.trans
      ((exponentTupleEquiv _).symm.trans
        (q.symm.arrowCongr (Equiv.refl ℕ))).toEmbedding =
      (q.symm.arrowCongr (Equiv.refl ℕ)).toEmbedding := by
    ext a i
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.trans_apply,
      Equiv.symm_apply_apply]
  rw [decorationTuplesOfLabels, Finset.map_map, hmap]
  simp only [Finset.mem_map, Finset.Nat.mem_antidiagonalTuple, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨b, hb, rfl⟩
    change (∑ i, b (q i)) = total
    rw [Fintype.sum_equiv q (fun i ↦ b (q i)) b (fun _ ↦ rfl)]
    exact hb
  · intro ha
    refine ⟨fun j ↦ a (q.symm j), ?_, ?_⟩
    · rw [Fintype.sum_equiv q.symm (fun j ↦ a (q.symm j)) a (fun _ ↦ rfl)]
      exact ha
    · funext i
      change a (q.symm (q i)) = a i
      rw [Equiv.symm_apply_apply]

/-- Finite exponent tuples of a prescribed unweighted sum. The finite set
does not depend on the auxiliary enumeration of external labels. -/
def decorationTuples (S : Type) [Fintype S] [DecidableEq S] (v e d total : ℕ) :
    Finset (DecorationIndex S v e d → ℕ) :=
  (Fintype.truncEquivFin S).lift
    (fun labels ↦ decorationTuplesOfLabels labels v e d total)
    (by
      intro labels₁ labels₂
      ext a
      rw [mem_decorationTuplesOfLabels, mem_decorationTuplesOfLabels])

/-- Dense tuple construction contains exactly the functions of the given sum. -/
theorem mem_decorationTuples {S : Type} [Fintype S] [DecidableEq S]
    (v e d total : ℕ) (a : DecorationIndex S v e d → ℕ) :
    a ∈ decorationTuples S v e d total ↔ ∑ i, a i = total := by
  unfold decorationTuples
  induction Fintype.truncEquivFin S using Trunc.ind with
  | _ labels =>
    rw [Trunc.lift_mk, mem_decorationTuplesOfLabels]

/-- Explicit indexing produces exactly mathlib's antidiagonal finite set. -/
theorem decorationTuples_eq_piAntidiag (S : Type) [Fintype S] [DecidableEq S]
    (v e d total : ℕ) :
    decorationTuples S v e d total = Finset.piAntidiag Finset.univ total := by
  ext a
  simp only [mem_decorationTuples, Finset.mem_piAntidiag, Finset.mem_univ,
    implies_true, and_true]

/-- Weighted codimension of a finite decoration vector. -/
def decorationDegree {S : Type} [Fintype S] {v e d : ℕ}
    (a : DecorationIndex S v e d → ℕ) : ℕ := ∑ i, decorationWeight i * a i

/-- Search only explicitly indexed tuples whose unweighted degree fits the
budget, then apply the positive kappa weights. -/
def decorations (S : Type) [Fintype S] [DecidableEq S] (v e d budget : ℕ) :
    Finset (DecorationIndex S v e d → ℕ) :=
  if budget = 0 then {0} else
    ((Finset.range (budget + 1)).biUnion fun k ↦ decorationTuples S v e d k).filter
      (fun a ↦ decorationDegree a ≤ budget)

/-- Explicit indexing leaves the standard finite exponent search unchanged.
This equality also supports kernel checking of the small numerical fixtures. -/
theorem decorations_eq_standard (S : Type) [Fintype S] [DecidableEq S]
    (v e d budget : ℕ) :
    decorations S v e d budget =
      ((Finset.range (budget + 1)).biUnion fun k ↦ Finset.piAntidiag Finset.univ k).filter
        (fun a : DecorationIndex S v e d → ℕ ↦ decorationDegree a ≤ budget) := by
  unfold decorations
  split_ifs with h
  · subst budget
    simp only [zero_add, Finset.range_one, Finset.singleton_biUnion, Finset.piAntidiag_zero,
      Finset.filter_singleton, decorationDegree, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, le_refl, ite_true]
  · simp only [decorationTuples_eq_piAntidiag]

/-- The exponent search contains exactly the decoration vectors in budget. -/
theorem mem_decorations {S : Type} [Fintype S] [DecidableEq S]
    (v e d budget : ℕ) (a : DecorationIndex S v e d → ℕ) :
    a ∈ decorations S v e d budget ↔ decorationDegree a ≤ budget := by
  simp only [decorations_eq_standard, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Finset.mem_biUnion.mpr ⟨∑ i, a i, ?_, ?_⟩, h⟩
    · apply Finset.mem_range.mpr
      have hsum : (∑ i, a i) ≤ decorationDegree a := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.le_mul_of_pos_left _ (decorationWeight_pos i)
      omega
    · exact Finset.mem_piAntidiag.mpr ⟨rfl, fun _ _ ↦ Finset.mem_univ _⟩

/-- Positive kappa index corresponding to the zero-based vector position. -/
def kappaIndex (d : ℕ) : Fin d ↪ ℕ+ where
  toFun i := ⟨i.1 + 1, Nat.succ_pos _⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact Nat.add_right_cancel (congrArg Subtype.val h)

/-- A computable finitely supported kappa monomial from bounded indices. -/
def kappaVector (d : ℕ) (a : Fin d → ℕ) : ℕ+ →₀ ℕ where
  support := (Finset.univ.filter fun i : Fin d ↦ a i ≠ 0).map (kappaIndex d)
  toFun k := if h : (k : ℕ) ≤ d then
    a ⟨(k : ℕ) - 1, lt_of_lt_of_le (Nat.sub_lt k.2 Nat.one_pos) h⟩ else 0
  mem_support_toFun := by
    intro k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hik⟩
      subst k
      change (if h : i.val + 1 ≤ d then a ⟨(i.val + 1) - 1, _⟩ else 0) ≠ 0
      have h : i.val + 1 ≤ d := by omega
      simpa only [h, ↓reduceDIte, Nat.add_sub_cancel] using hi
    · intro hk
      by_cases h : (k : ℕ) ≤ d
      · refine ⟨⟨(k : ℕ) - 1,
          lt_of_lt_of_le (Nat.sub_lt k.2 Nat.one_pos) h⟩, ?_, ?_⟩
        · simpa only [h, ↓reduceDIte] using hk
        · apply Subtype.ext
          exact Nat.sub_add_cancel (Nat.succ_le_of_lt k.2)
      · simp only [h, ↓reduceDIte, ne_eq, not_true_eq_false] at hk

/-- Evaluating an encoded positive kappa index returns its exponent. -/
theorem kappaVector_apply_index (d : ℕ) (a : Fin d → ℕ) (i : Fin d) :
    kappaVector d a (kappaIndex d i) = a i := by
  change (if h : i.val + 1 ≤ d then a ⟨(i.val + 1) - 1, _⟩ else 0) = a i
  have h : i.val + 1 ≤ d := by omega
  simp only [h, ↓reduceDIte, Nat.add_sub_cancel]

/-- The kappa-vector encoding preserves weighted codimension. -/
theorem kappaVector_sum (d : ℕ) (a : Fin d → ℕ) :
    (kappaVector d a).sum (fun i p ↦ (i : ℕ) * p) = ∑ i, (i.1 + 1) * a i := by
  rw [Finsupp.sum]
  change (∑ k ∈ (Finset.univ.filter fun i : Fin d ↦ a i ≠ 0).map (kappaIndex d),
    (k : ℕ) * kappaVector d a k) = _
  rw [Finset.sum_map]
  simp only [kappaVector_apply_index]
  change (∑ i ∈ Finset.univ.filter (fun i : Fin d ↦ a i ≠ 0),
    (i.1 + 1) * a i) = ∑ i, (i.1 + 1) * a i
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · rw [not_ne_iff] at h
    rw [h, mul_zero]

/-- Decoding a vector of the whole bounded support preserves the original
kappa monomial. -/
theorem kappaVector_truncate (d : ℕ) (f : ℕ+ →₀ ℕ)
    (hf : ∀ i : ℕ+, d < (i : ℕ) → f i = 0) :
    kappaVector d (fun i ↦ f (kappaIndex d i)) = f := by
  apply Finsupp.ext
  intro k
  change (if h : (k : ℕ) ≤ d then _ else 0) = f k
  by_cases h : (k : ℕ) ≤ d
  · rw [dif_pos h]
    congr 1
    apply Subtype.ext
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt k.2)
  · rw [dif_neg h, hf k (Nat.lt_of_not_ge h)]

/-- Interpret finite decoration coordinates on a checked graph candidate. -/
def toDecoration {S : Type} [Fintype S] {g v e d : ℕ}
    (c : StableGraphCode.Candidate S v e) (h : c.Valid g)
    (a : DecorationIndex S v e d → ℕ) : DecoratedStableGraph S :=
  let kappa := Vector.ofFn (fun vertex : Fin v ↦
    kappaVector d (fun i ↦ a (.inl (vertex, i))))
  { graph := c.toGraph h
    kappaPower vertex := kappa[vertex.1]
    legPsiPower s := a (.inr (.inl s))
    halfEdgePsiPower edge i := a (.inr (.inr (edge, i))) }

/-- The materialized interpretation equals the direct graph constructor.
This form permits kernel evaluation without reducing vector internals. -/
theorem toDecoration_eq_mk {S : Type} [Fintype S] {g v e d : ℕ}
    (c : StableGraphCode.Candidate S v e) (h : c.Valid g)
    (a : DecorationIndex S v e d → ℕ) :
    toDecoration c h a =
      { graph := c.toGraph h
        kappaPower vertex := kappaVector d (fun i ↦ a (.inl (vertex, i)))
        legPsiPower s := a (.inr (.inl s))
        halfEdgePsiPower edge i := a (.inr (.inr (edge, i))) } := by
  simp only [toDecoration, Vector.getElem_ofFn, Fin.eta]

/-- Materializing kappa monomials preserves their powers on every vertex. -/
theorem toDecoration_kappaPower {S : Type} [Fintype S] {g v e d : ℕ}
    (c : StableGraphCode.Candidate S v e) (h : c.Valid g)
    (a : DecorationIndex S v e d → ℕ) (vertex : Fin v) :
    (toDecoration c h a).kappaPower vertex =
      kappaVector d (fun i ↦ a (.inl (vertex, i))) := by
  simp only [toDecoration, Vector.getElem_ofFn]

/-- Decoration leaves the requested arithmetic genus unchanged. -/
theorem toDecoration_totalGenus {S : Type} [Fintype S] {g v e d : ℕ}
    (c : StableGraphCode.Candidate S v e) (h : c.Valid g)
    (a : DecorationIndex S v e d → ℕ) :
    (toDecoration c h a).graph.totalGenus = g := c.toGraph_totalGenus h

/-- Decoding preserves the complete edge-plus-decoration codimension. -/
theorem toDecoration_codimension {S : Type} [Fintype S] {g v e d : ℕ}
    (c : StableGraphCode.Candidate S v e) (h : c.Valid g)
    (a : DecorationIndex S v e d → ℕ) :
    (toDecoration c h a).codimension = e + decorationDegree a := by
  unfold codimension kappaCodimension legPsiCodimension halfEdgePsiCodimension
    decorationDegree
  simp only [toDecoration, Vector.getElem_ofFn, StableGraphCode.Candidate.toGraph,
    kappaVector_sum, Fintype.sum_sum_type, Fintype.sum_prod_type, decorationWeight, one_mul]
  ac_rfl

/-- Encode a decorated graph's exponents using a bounded positive-index
kappa range. Larger kappa indices are omitted only when their powers vanish. -/
def decorationVector {S : Type} [Fintype S] (G : DecoratedStableGraph S) (d : ℕ) :
    DecorationIndex S G.graph.vertexCount G.graph.edgeCount d → ℕ
  | .inl (vertex, i) => G.kappaPower vertex (kappaIndex d i)
  | .inr (.inl s) => G.legPsiPower s
  | .inr (.inr (edge, i)) => G.halfEdgePsiPower edge i

/-- Encoding and decoding are exact throughout the codimension bound. -/
theorem toDecoration_decorationVector {S : Type} [Fintype S]
    (G : DecoratedStableGraph S) {g d : ℕ} (hg : G.graph.totalGenus = g)
    (hd : G.codimension ≤ d) :
    toDecoration (StableGraphCode.Candidate.ofGraph G.graph)
      (StableGraphCode.Candidate.ofGraph_valid G.graph hg) (decorationVector G d) = G := by
  have hk : (fun vertex ↦ kappaVector d
      (fun i ↦ G.kappaPower vertex (kappaIndex d i))) = G.kappaPower := by
    funext vertex
    exact kappaVector_truncate d (G.kappaPower vertex) fun i hi ↦
      G.kappaPower_eq_zero_of_codimension_lt vertex i (lt_of_le_of_lt hd hi)
  cases G
  change DecoratedStableGraph.mk _ _ _ _ = _
  simp only [Vector.getElem_ofFn]
  congr 1

/-- The exponent vector of every bounded graph passes the budget check. -/
theorem decorationVector_degree_le {S : Type} [Fintype S]
    (G : DecoratedStableGraph S) {g d : ℕ} (hg : G.graph.totalGenus = g)
    (hd : G.codimension ≤ d) :
    decorationDegree (decorationVector G d) ≤ d - G.graph.edgeCount := by
  have h := toDecoration_codimension (StableGraphCode.Candidate.ofGraph G.graph)
    (StableGraphCode.Candidate.ofGraph_valid G.graph hg) (decorationVector G d)
  rw [toDecoration_decorationVector G hg hd] at h
  omega

end DecoratedStableGraph

namespace TautologicalStratum

/-- A presentation-independent integer key for the external leg relation,
using an explicit enumeration of the labels. Equal keys only select a search
group; equality of strata still uses the complete isomorphism test. -/
def legRelationKey {g : ℕ} {S : Type} [Fintype S]
    (labels : S ≃ Fin (Fintype.card S)) (x : TautologicalStratum g S) : ℕ :=
  Quotient.liftOn x (fun G ↦ ∑ s, ∑ t,
    if G.1.graph.legVertex s = G.1.graph.legVertex t then
      2 ^ ((labels s).1 * Fintype.card S + (labels t).1) else 0)
    (by
      intro G H h
      rcases h with ⟨e⟩
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      simp only [e.graphIso.legVertex_eq_iff s t])

/-- Materialize invariant keys before comparing semantic classes, so
isomorphism tests only run within a single leg-relation group. -/
def imageByLegRelation {α : Type} {g : ℕ} {S : Type}
    [Fintype S] (labels : S ≃ Fin (Fintype.card S)) (s : Finset α)
    (f : α → TautologicalStratum g S) : Finset (TautologicalStratum g S) := by
  let packed := s.map
    ⟨fun a ↦ (legRelationKey labels (f a), a), fun _ _ h ↦ congrArg Prod.snd h⟩
  let bucket := fun key : ℕ ↦
    (packed.filter (fun p ↦ p.1 = key)).image (fun p ↦ f p.2)
  have hkey : ∀ key x, x ∈ bucket key → legRelationKey labels x = key := by
    intro key x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨hp, hkey⟩
    rcases Finset.mem_map.mp hp with ⟨a, _, rfl⟩
    exact hkey
  exact (packed.image Prod.fst).disjiUnion bucket (by
    intro key _ key' _ hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact hne ((hkey key x hx).symm.trans (hkey key' x hx')))

/-- Grouping by a semantic invariant preserves the entire finite image. -/
theorem imageByLegRelation_eq {α : Type} {g : ℕ} {S : Type}
    [Fintype S] (labels : S ≃ Fin (Fintype.card S)) (s : Finset α)
    (f : α → TautologicalStratum g S) :
    imageByLegRelation labels s f = s.image f := by
  classical
  unfold imageByLegRelation
  ext x
  simp only [Finset.mem_disjiUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨key, _, p, ⟨⟨a, ha, hap⟩, _⟩, hf⟩
    subst p
    exact ⟨a, ha, hf⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨legRelationKey labels (f a),
      ⟨(legRelationKey labels (f a), a), ⟨a, ha, rfl⟩, rfl⟩,
      (legRelationKey labels (f a), a), ⟨⟨a, ha, rfl⟩, rfl⟩, hx⟩
variable (S : Type) [Fintype S] [DecidableEq S]

/-- Enumerate strata with fixed numbers of vertices and edges, including
all codimension-compatible decorations. -/
def strataAtSize (g d v e : ℕ) : Finset (TautologicalStratum g S) :=
  if e ≤ d then
    (Fintype.truncEquivFin S).lift
      (fun labels ↦ imageByLegRelation labels
        ((StableGraphCode.candidates S g v e).attach.product
          (DecoratedStableGraph.decorations S v e d (d - e))) fun pair ↦
            let c := pair.1
            let h := (StableGraphCode.mem_candidates S g v e c.1).1 c.2
            mk (DecoratedStableGraph.toDecoration c.1 h pair.2)
              (DecoratedStableGraph.toDecoration_totalGenus c.1 h pair.2))
      (by
        intro labels₁ labels₂
        rw [imageByLegRelation_eq, imageByLegRelation_eq])
  else ∅

/-- Grouping by the leg relation preserves the standard fixed-size image.
This equality supports proofs and kernel evaluation of small fixtures. -/
theorem strataAtSize_eq_standard (g d v e : ℕ) :
    strataAtSize S g d v e =
      if e ≤ d then
        ((StableGraphCode.candidates S g v e).attach.product
          (DecoratedStableGraph.decorations S v e d (d - e))).image fun pair ↦
            let c := pair.1
            let h := (StableGraphCode.mem_candidates S g v e c.1).1 c.2
            mk (DecoratedStableGraph.toDecoration c.1 h pair.2)
              (DecoratedStableGraph.toDecoration_totalGenus c.1 h pair.2)
      else ∅ := by
  unfold strataAtSize
  split_ifs
  · induction Fintype.truncEquivFin S using Trunc.ind with
    | _ labels => rw [Trunc.lift_mk, imageByLegRelation_eq]
  · rfl

/-- A proof-facing fixed-size image whose candidate type records graph
validity rather than membership in the optimized search. -/
theorem strataAtSize_eq_semantic (g d v e : ℕ) :
    strataAtSize S g d v e =
      if e ≤ d then
        ((StableGraphCode.validCandidates S g v e).product
          (DecoratedStableGraph.decorations S v e d (d - e))).image fun pair ↦
            mk (DecoratedStableGraph.toDecoration pair.1.1 pair.1.2 pair.2)
              (DecoratedStableGraph.toDecoration_totalGenus pair.1.1 pair.1.2 pair.2)
      else ∅ := by
  rw [strataAtSize_eq_standard]
  split_ifs
  · ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨⟨c, a⟩, hpair, hx⟩
      let cv : {c : StableGraphCode.Candidate S v e // c.Valid g} :=
        ⟨c.1, (StableGraphCode.mem_candidates S g v e c.1).1 c.2⟩
      exact Finset.mem_image.mpr ⟨(cv, a),
        Finset.mem_product.mpr ⟨StableGraphCode.mem_validCandidates S g v e cv,
          (Finset.mem_product.mp hpair).2⟩, hx⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨⟨c, a⟩, hpair, hx⟩
      let ca : {c : StableGraphCode.Candidate S v e //
          c ∈ StableGraphCode.candidates S g v e} :=
        ⟨c.1, (StableGraphCode.mem_candidates S g v e c.1).2 c.2⟩
      exact Finset.mem_image.mpr ⟨(ca, a),
        Finset.mem_product.mpr ⟨Finset.mem_attach _ _,
          (Finset.mem_product.mp hpair).2⟩, hx⟩
  · rfl

/-- Fixed-size searches produce precisely their declared vertex and edge
counts. These quotient invariants separate different size groups. -/
theorem counts_of_mem_strataAtSize (g d v e : ℕ) (x : TautologicalStratum g S)
    (hx : x ∈ strataAtSize S g d v e) :
    x.vertexCount = v ∧ x.edgeCount = e := by
  rw [strataAtSize_eq_standard] at hx
  split_ifs at hx
  · rcases Finset.mem_image.mp hx with ⟨⟨c, a⟩, _, rfl⟩
    exact ⟨rfl, rfl⟩
  · exact False.elim (Finset.notMem_empty _ hx)

/-- Every stratum produced by the fixed-size search is in the requested
codimension range. -/
theorem codimension_le_of_mem_strataAtSize (g d v e : ℕ)
    (x : TautologicalStratum g S) (hx : x ∈ strataAtSize S g d v e) :
    x.codimension ≤ d := by
  rw [strataAtSize_eq_standard] at hx
  split_ifs at hx with he
  · rcases Finset.mem_image.mp hx with ⟨⟨c, a⟩, hpair, rfl⟩
    have ha := (DecoratedStableGraph.mem_decorations v e d (d - e) a).1
      (Finset.mem_product.mp hpair).2
    rw [codimension_mk, DecoratedStableGraph.toDecoration_codimension]
    change e + DecoratedStableGraph.decorationDegree a ≤ d
    omega
  · exact False.elim (Finset.notMem_empty _ hx)

/-- Every bounded decorated presentation occurs in its fixed-size search. -/
theorem mk_mem_strataAtSize (G : DecoratedStableGraph S) {g d : ℕ}
    (hg : G.graph.totalGenus = g) (hd : G.codimension ≤ d) :
    mk G hg ∈ strataAtSize S g d G.graph.vertexCount G.graph.edgeCount := by
  have he : G.graph.edgeCount ≤ d := G.edgeCount_le_codimension.trans hd
  rw [strataAtSize_eq_standard, if_pos he]
  let c := StableGraphCode.Candidate.ofGraph G.graph
  have hc : c ∈ StableGraphCode.candidates S g G.graph.vertexCount G.graph.edgeCount :=
    (StableGraphCode.mem_candidates S _ _ _ c).2
      (StableGraphCode.Candidate.ofGraph_valid G.graph hg)
  let a := DecoratedStableGraph.decorationVector G d
  have ha : a ∈ DecoratedStableGraph.decorations S G.graph.vertexCount
      G.graph.edgeCount d (d - G.graph.edgeCount) :=
    (DecoratedStableGraph.mem_decorations _ _ _ _ a).2
      (G.decorationVector_degree_le hg hd)
  refine Finset.mem_image.mpr ⟨(⟨c, hc⟩, a), Finset.mem_product.mpr
    ⟨Finset.mem_attach _ _, ha⟩, ?_⟩
  dsimp only
  apply congrArg (Quotient.mk _)
  exact Subtype.ext (DecoratedStableGraph.toDecoration_decorationVector G hg hd)

/-- Enumerate every decorated stratum through codimension `d`. The spanning
tree bound limits vertices to `e + 1`; the edge contribution bounds `e` by
`d`. Distinct vertex/edge counts give disjoint groups, avoiding repeated
isomorphism comparisons when joining those groups. -/
def boundedStrata (g d : ℕ) : Finset (TautologicalStratum g S) :=
  (Finset.range (d + 1)).disjiUnion
    (fun e ↦ (Finset.range (e + 1)).disjiUnion
      (fun v ↦ strataAtSize S g d (v + 1) e)
      (by
        intro v _ v' _ hne
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        have hv := (counts_of_mem_strataAtSize S g d (v + 1) e x hx).1
        have hv' := (counts_of_mem_strataAtSize S g d (v' + 1) e x hx').1
        exact hne (Nat.add_right_cancel (hv.symm.trans hv'))))
    (by
      intro e _ e' _ hne
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      rcases Finset.mem_disjiUnion.mp hx with ⟨v, _, hx⟩
      rcases Finset.mem_disjiUnion.mp hx' with ⟨v', _, hx'⟩
      have he := (counts_of_mem_strataAtSize S g d (v + 1) e x hx).2
      have he' := (counts_of_mem_strataAtSize S g d (v' + 1) e' x hx').2
      exact hne (he.symm.trans he'))

/-- All enumerated strata satisfy the declared codimension bound. -/
theorem codimension_le_of_mem_boundedStrata (g d : ℕ) (x : TautologicalStratum g S)
    (hx : x ∈ boundedStrata S g d) : x.codimension ≤ d := by
  rcases Finset.mem_disjiUnion.mp hx with ⟨e, _, hx⟩
  rcases Finset.mem_disjiUnion.mp hx with ⟨v, _, hx⟩
  exact codimension_le_of_mem_strataAtSize S g d (v + 1) e x hx

/-- Completeness applies to arbitrary genus, markings, and finite degree
bounds, including loops, repeated edges, and arbitrary positive kappa indices. -/
theorem mk_mem_boundedStrata (G : DecoratedStableGraph S) {g d : ℕ}
    (hg : G.graph.totalGenus = g) (hd : G.codimension ≤ d) :
    mk G hg ∈ boundedStrata S g d := by
  have he : G.graph.edgeCount < d + 1 :=
    Nat.lt_succ_of_le (G.edgeCount_le_codimension.trans hd)
  have hv : G.graph.vertexCount - 1 < G.graph.edgeCount + 1 := by
    have := G.graph.vertexCount_le_edgeCount_add_one
    have := G.graph.vertexCount_pos
    omega
  have hv_eq : G.graph.vertexCount - 1 + 1 = G.graph.vertexCount := by
    have := G.graph.vertexCount_pos
    omega
  apply Finset.mem_disjiUnion.mpr
  refine ⟨G.graph.edgeCount, Finset.mem_range.mpr he, Finset.mem_disjiUnion.mpr ?_⟩
  refine ⟨G.graph.vertexCount - 1, Finset.mem_range.mpr hv, ?_⟩
  rw [hv_eq]
  exact mk_mem_strataAtSize S G hg hd

/-- The executable finite corpus is exactly the bounded part of the existing
stratum quotient. No graph or decoration completeness assumption is required. -/
theorem mem_boundedStrata (g d : ℕ) (x : TautologicalStratum g S) :
    x ∈ boundedStrata S g d ↔ x.codimension ≤ d := by
  constructor
  · exact codimension_le_of_mem_boundedStrata S g d x
  · intro hx
    induction x using Quotient.inductionOn with
    | h G => exact mk_mem_boundedStrata S G.1 G.2 hx

end TautologicalStratum
end AxiomaticGW
