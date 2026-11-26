/- Candidate marked WDVV replay. Geometric boundary equality remains a hypothesis.
Input SHA256:
44ba7410c29fd82126c188d52e0203f7aaa38139c315c7317e6221a6d905284d
This digest is provenance, not proof. -/
module

public import AxiomaticGW.Tautological.WDVVRealization

public import AxiomaticGW.Tautological.GraphEnumeration

@[expose] public section

namespace AxiomaticGW.WDVVReplay

def incomingGraph0Candidate : StableGraphCode.Candidate (Fin 4) 2 1 where
  legVertex := ![0, 0, 1, 1]
  endpoint := ![![0, 1]]
  genus := ![0, 0]

theorem incomingGraph0Valid : incomingGraph0Candidate.Valid 0 := by decide

def incomingGraph0Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 1 1 → ℕ
  | .inl (vertex, index) => (![![0], ![0]] : Fin 2 → Fin 1 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

def incomingGraph0 : TautologicalStratum 0 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)

theorem incomingGraph0_eq : incomingGraph0 = WDVV.columns 0 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph0Candidate incomingGraph0Valid incomingGraph0Exponents)
    (WDVV.graph_totalGenus 0)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph1Candidate : StableGraphCode.Candidate (Fin 4) 2 1 where
  legVertex := ![0, 1, 0, 1]
  endpoint := ![![0, 1]]
  genus := ![0, 0]

theorem incomingGraph1Valid : incomingGraph1Candidate.Valid 0 := by decide

def incomingGraph1Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 1 1 → ℕ
  | .inl (vertex, index) => (![![0], ![0]] : Fin 2 → Fin 1 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

def incomingGraph1 : TautologicalStratum 0 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)

theorem incomingGraph1_eq : incomingGraph1 = WDVV.columns 1 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph1Candidate incomingGraph1Valid incomingGraph1Exponents)
    (WDVV.graph_totalGenus 1)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingGraph2Candidate : StableGraphCode.Candidate (Fin 4) 2 1 where
  legVertex := ![0, 1, 1, 0]
  endpoint := ![![0, 1]]
  genus := ![0, 0]

theorem incomingGraph2Valid : incomingGraph2Candidate.Valid 0 := by decide

def incomingGraph2Exponents : DecoratedStableGraph.DecorationIndex (Fin 4) 2 1 1 → ℕ
  | .inl (vertex, index) => (![![0], ![0]] : Fin 2 → Fin 1 → ℕ)
      vertex index
  | .inr (.inl label) => (![0, 0, 0, 0]) label
  | .inr (.inr (edge, branch)) => (![![0, 0]]) edge branch

def incomingGraph2 : TautologicalStratum 0 (Fin 4) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)

theorem incomingGraph2_eq : incomingGraph2 = WDVV.columns 2 :=
  TautologicalStratum.mk_eq_mk_of_isomorphic?
    (DecoratedStableGraph.toDecoration_totalGenus
      incomingGraph2Candidate incomingGraph2Valid incomingGraph2Exponents)
    (WDVV.graph_totalGenus 2)
    (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide)

def incomingColumns : Fin 3 → TautologicalStratum 0 (Fin 4) :=
  ![incomingGraph0, incomingGraph1, incomingGraph2]

def presentation : RelationCertificate.Presentation 0 (Fin 4) 2 3 where
  columns := incomingColumns
  columnFactors := ![1, 1, 1]
  rows := ![![1, -1, 0],
    ![0, 1, -1]]
  claimedRequest := ![1, 0, -1]
  certificate := ⟨![1, 1]⟩

theorem accepted : WDVV.AcceptsExchange presentation := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change incomingColumns = WDVV.columns
      funext i
      fin_cases i
      · exact incomingGraph0_eq
      · exact incomingGraph1_eq
      · exact incomingGraph2_eq
    · funext i
      fin_cases i <;> norm_num [presentation, Matrix.cons_val_two]
    · rfl
    · rfl
  · funext i
    fin_cases i <;>
      norm_num [RelationCertificate.combination, presentation, WDVV.rows,
        WDVV.requested, Fin.sum_univ_two, Matrix.cons_val_two]

/-- Offline replay certifies the held formal consequence in the fixed row span. -/
theorem requested_mem_relationSpan :
    RelationCertificate.interpret WDVV.columns WDVV.requested ∈
      RelationCertificate.relationSpan WDVV.columns WDVV.rows :=
  RelationCertificate.acceptsPresentation_sound _ _ _ presentation accepted

end AxiomaticGW.WDVVReplay
