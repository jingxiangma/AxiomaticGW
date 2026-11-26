/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GraphEnumeration
public import AxiomaticGW.Tautological.RelationCertificate
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Fixed admcycles genus-two relation frame

This is the reviewed unmarked codimension-two frame from the pinned admcycles
1.4 FZ_matrix(2, 2) fixture. Its eight columns are explicit raw gluing
pushforwards with monomial kappa decorations. The rational row tables and
request are fixed here, independently of incoming replay data. No geometric
vanishing of these rows is asserted. The source report SHA256 is
142c06e43218a470cd90daee0064ea6c2b49bbe37dba0372441c8ee4a75244b0.
-/

@[expose] public section

namespace AxiomaticGW.AdmcyclesGenusTwo

open RelationCertificate

/-- One genus-two vertex without edges, underlying the kappa_2 column. -/
def graph0Candidate : StableGraphCode.Candidate (Fin 0) 1 0 where
  legVertex := Fin.elim0
  endpoint := Fin.elim0
  genus := ![2]

theorem graph0Valid : graph0Candidate.Valid 2 := by decide

/-- The single kappa_2 decoration, with every other exponent zero. -/
def graph0Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![0, 1]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- Raw one-vertex column decorated by kappa_2. -/
def graph0 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph0Candidate graph0Valid graph0Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph0Candidate graph0Valid graph0Exponents)

/-- One genus-two vertex without edges, underlying the kappa_1-squared column. -/
def graph1Candidate : StableGraphCode.Candidate (Fin 0) 1 0 where
  legVertex := Fin.elim0
  endpoint := Fin.elim0
  genus := ![2]

theorem graph1Valid : graph1Candidate.Valid 2 := by decide

/-- The kappa_1 exponent two on the single vertex. -/
def graph1Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 1 0 2 → ℕ
  | .inl (vertex, index) => (![![2, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, _)) => Fin.elim0 edge

/-- Raw one-vertex column decorated by kappa_1 squared. -/
def graph1 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph1Candidate graph1Valid graph1Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph1Candidate graph1Valid graph1Exponents)

/-- Two genus-one vertices joined by a separating edge. -/
def graph2Candidate : StableGraphCode.Candidate (Fin 0) 2 1 where
  legVertex := Fin.elim0
  endpoint := ![![0, 1]]
  genus := ![1, 1]

theorem graph2Valid : graph2Candidate.Valid 2 := by decide

/-- One kappa_1 factor at vertex zero and zero branch psi powers. -/
def graph2Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, branch)) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) edge branch

/-- Raw separating column decorated by kappa_1 on its first vertex. -/
def graph2 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph2Candidate graph2Valid graph2Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph2Candidate graph2Valid graph2Exponents)

/-- Two genus-one vertices joined by the edge carrying the branch decoration. -/
def graph3Candidate : StableGraphCode.Candidate (Fin 0) 2 1 where
  legVertex := Fin.elim0
  endpoint := ![![0, 1]]
  genus := ![1, 1]

theorem graph3Valid : graph3Candidate.Valid 2 := by decide

/-- One psi factor on the edge branch at vertex zero and no kappa factors. -/
def graph3Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 2 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, branch)) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) edge branch

/-- Raw separating column with a cotangent factor on its first branch. -/
def graph3 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph3Candidate graph3Valid graph3Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph3Candidate graph3Valid graph3Exponents)

/-- One genus-one vertex with a nonseparating loop. -/
def graph4Candidate : StableGraphCode.Candidate (Fin 0) 1 1 where
  legVertex := Fin.elim0
  endpoint := ![![0, 0]]
  genus := ![1]

theorem graph4Valid : graph4Candidate.Valid 2 := by decide

/-- One kappa_1 factor at the loop vertex and zero branch psi powers. -/
def graph4Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, branch)) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) edge branch

/-- Raw nonseparating column decorated by kappa_1. -/
def graph4 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph4Candidate graph4Valid graph4Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph4Candidate graph4Valid graph4Exponents)

/-- One genus-one vertex with the loop carrying the branch decoration. -/
def graph5Candidate : StableGraphCode.Candidate (Fin 0) 1 1 where
  legVertex := Fin.elim0
  endpoint := ![![0, 0]]
  genus := ![1]

theorem graph5Valid : graph5Candidate.Valid 2 := by decide

/-- One psi factor on branch zero of the loop and no kappa factors. -/
def graph5Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 1 1 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, branch)) => (![![1, 0]] : Fin 1 → Fin 2 → ℕ) edge branch

/-- Raw nonseparating column with one decorated loop branch. -/
def graph5 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph5Candidate graph5Valid graph5Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph5Candidate graph5Valid graph5Exponents)

/-- A genus-zero loop vertex joined to a genus-one vertex by a second edge. -/
def graph6Candidate : StableGraphCode.Candidate (Fin 0) 2 2 where
  legVertex := Fin.elim0
  endpoint := ![![0, 0], ![0, 1]]
  genus := ![0, 1]

theorem graph6Valid : graph6Candidate.Valid 2 := by decide

/-- All kappa and psi exponents are zero in the two-edge presentation. -/
def graph6Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 2 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) edge branch

/-- Raw loop-and-separating-edge column with no additional decorations. -/
def graph6 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph6Candidate graph6Valid graph6Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph6Candidate graph6Valid graph6Exponents)

/-- One genus-zero vertex with two nonseparating loops. -/
def graph7Candidate : StableGraphCode.Candidate (Fin 0) 1 2 where
  legVertex := Fin.elim0
  endpoint := ![![0, 0], ![0, 0]]
  genus := ![0]

theorem graph7Valid : graph7Candidate.Valid 2 := by decide

/-- All kappa and psi exponents are zero in the two-loop presentation. -/
def graph7Exponents : DecoratedStableGraph.DecorationIndex (Fin 0) 1 2 2 → ℕ
  | .inl (vertex, index) => (![![0, 0]] : Fin 1 → Fin 2 → ℕ) vertex index
  | .inr (.inl label) => Fin.elim0 label
  | .inr (.inr (edge, branch)) => (![![0, 0], ![0, 0]] : Fin 2 → Fin 2 → ℕ) edge branch

/-- Raw two-loop column with no additional decorations. -/
def graph7 : TautologicalStratum 2 (Fin 0) :=
  TautologicalStratum.mk
    (DecoratedStableGraph.toDecoration
      graph7Candidate graph7Valid graph7Exponents)
    (DecoratedStableGraph.toDecoration_totalGenus
      graph7Candidate graph7Valid graph7Exponents)

/-- Fixed raw graph columns in the pinned source order. -/
def columns : Fin 8 → TautologicalStratum 2 (Fin 0) :=
  ![graph0, graph1, graph2, graph3, graph4, graph5, graph6, graph7]

/-- Every column has the claimed genus-two codimension. -/
theorem columns_codimension : ∀ i, (columns i).codimension = 2 := by
  simp only [columns, graph0, graph1, graph2, graph3, graph4, graph5, graph6, graph7,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide

/-- The eight columns represent different graph-isomorphism classes. -/
theorem columns_injective : Function.Injective columns := by
  simp only [columns, graph0, graph1, graph2, graph3, graph4, graph5, graph6, graph7,
    DecoratedStableGraph.toDecoration_eq_mk]
  decide

set_option maxRecDepth 10000 in
/-- The fixed frame is exactly the full formal codimension-two corpus, not
merely eight arbitrary graphs with an agreeing cardinality. -/
theorem columns_eq_exactCorpus : Finset.univ.image columns =
    (TautologicalStratum.boundedStrata (Fin 0) 2 2).filter
      (fun x ↦ x.codimension = 2) := by
  have hcard : ((TautologicalStratum.boundedStrata (Fin 0) 2 2).filter
      (fun x ↦ x.codimension = 2)).card = 8 := by
    simp only [TautologicalStratum.boundedStrata, TautologicalStratum.strataAtSize_eq_semantic,
      StableGraphCode.validCandidates_eq_standard, StableGraphCode.standardCandidates,
      DecoratedStableGraph.decorations_eq_standard, DecoratedStableGraph.toDecoration_eq_mk]
    decide
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨(TautologicalStratum.mem_boundedStrata (Fin 0) 2 2 (columns i)).2 ?_,
      columns_codimension i⟩
    exact (columns_codimension i).le
  · rw [hcard, Finset.card_image_of_injective _ columns_injective,
      Finset.card_univ, Fintype.card_fin]

/-- The reviewed FZ rows in monomial kappa coordinates. Their geometric
validity is a separate input, not a field of the certificate. -/
def rows : Fin 7 → Coordinates 8 :=
  ![![0, -60, 84, 0, 6, 0, 0, 0],
    ![373248, -100512, 33984, -10080, 6624, -10080, -288, -72],
    ![103680, -12240, 13536, -5040, 1584, -5040, -144, -36],
    ![0, 0, 102, -30, 0, 0, -3, 0],
    ![0, 0, 30, 42, 0, 0, -3, 0],
    ![0, 0, 0, 0, 66, -60, -6, -3],
    ![0, 0, 0, 0, 15, 6, -21, (-3 / 2)]]

/-- The corresponding source rows in pushforward kappa coordinates. -/
def pushforwardRows : Fin 7 → Coordinates 8 :=
  ![![60, -60, 84, 0, 6, 0, 0, 0],
    ![473760, -100512, 33984, -10080, 6624, -10080, -288, -72],
    ![115920, -12240, 13536, -5040, 1584, -5040, -144, -36],
    ![0, 0, 102, -30, 0, 0, -3, 0],
    ![0, 0, 30, 42, 0, 0, -3, 0],
    ![0, 0, 0, 0, 66, -60, -6, -3],
    ![0, 0, 0, 0, 15, 6, -21, (-3 / 2)]]

/-- Explicit coordinate conversion; the kappa_1^2 slot is nontrivial. -/
def pushforwardToMonomial : Fin 8 → Coordinates 8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Inverse coordinate conversion from the pinned fixture. -/
def monomialToPushforward : Fin 8 → Coordinates 8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- The exact requested expression, fixed independently of a certificate. -/
def requested : Coordinates 8 :=
  ![0, -60, 135, -15, -4, -4, (25 / 2), 1]

/-- The same source request before the explicit kappa coordinate conversion. -/
def requestedPushforward : Coordinates 8 :=
  ![60, -60, 135, -15, -4, -4, (25 / 2), 1]

/-- Linear interpretation of the source coordinate conversion. -/
def toMonomial : Coordinates 8 →ₗ[ℚ] Coordinates 8 :=
  Fintype.linearCombination ℚ pushforwardToMonomial

/-- Linear inverse conversion. -/
def toPushforward : Coordinates 8 →ₗ[ℚ] Coordinates 8 :=
  Fintype.linearCombination ℚ monomialToPushforward

/-- All source relation rows use the recorded conversion. -/
theorem rows_conversion : ∀ i, toMonomial (pushforwardRows i) = rows i := by
  intro i
  rw [toMonomial, linearCombination_eq_combination]
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num only [combination, pushforwardRows, rows, pushforwardToMonomial,
      Fin.sum_univ_succ, Fintype.sum_empty, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]

/-- The requested expression uses that same conversion. -/
theorem requested_conversion : toMonomial requestedPushforward = requested := by
  rw [toMonomial, linearCombination_eq_combination]
  ext j
  fin_cases j <;>
    norm_num only [combination, requestedPushforward, requested, pushforwardToMonomial,
      Fin.sum_univ_succ, Fintype.sum_empty, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]

/-- The two coordinate conversions are inverse on every rational vector.
This is a formal coordinate identity, not a geometric pushforward theorem. -/
theorem toPushforward_comp_toMonomial :
    toPushforward.comp toMonomial = LinearMap.id := by
  have hb : ∀ i : Fin 8,
      toPushforward (toMonomial (Pi.single i 1)) = (Pi.single i 1 : Coordinates 8) := by
    intro i
    rw [toMonomial, Fintype.linearCombination_apply_single, one_smul,
      toPushforward, linearCombination_eq_combination]
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num only [combination, pushforwardToMonomial, monomialToPushforward,
        Pi.single_apply, Fin.sum_univ_succ, Fintype.sum_empty,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ, if_true, if_false]
  apply LinearMap.pi_ext
  intro i q
  have hq : (Pi.single i q : Coordinates 8) = q • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using
      Pi.single_smul (f := fun _ : Fin 8 ↦ ℚ) i q (1 : ℚ)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, hq, map_smul, hb]

/-- The reverse composition is also the identity on all coordinates. -/
theorem toMonomial_comp_toPushforward :
    toMonomial.comp toPushforward = LinearMap.id := by
  have hb : ∀ i : Fin 8,
      toMonomial (toPushforward (Pi.single i 1)) = (Pi.single i 1 : Coordinates 8) := by
    intro i
    rw [toPushforward, Fintype.linearCombination_apply_single, one_smul,
      toMonomial, linearCombination_eq_combination]
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num only [combination, pushforwardToMonomial, monomialToPushforward,
        Pi.single_apply, Fin.sum_univ_succ, Fintype.sum_empty,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ, if_true, if_false]
  apply LinearMap.pi_ext
  intro i q
  have hq : (Pi.single i q : Coordinates 8) = q • Pi.single i 1 := by
    simpa only [smul_eq_mul, mul_one] using
      Pi.single_smul (f := fun _ : Fin 8 ↦ ℚ) i q (1 : ℚ)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, hq, map_smul, hb]

/-- Complete candidate data for this fixed fixture, including both source
coordinate tables. These fields do not supply geometric relation proofs. -/
structure Exchange where
  /-- Candidate monomial coordinates, semantic columns, and row witness. -/
  presentation : Presentation 2 (Fin 0) 7 8
  /-- Source relation rows before the recorded kappa conversion. -/
  sourceRows : Fin 7 → Coordinates 8
  /-- Source-to-destination coordinate table. -/
  sourceToMonomial : Fin 8 → Coordinates 8
  /-- Destination-to-source coordinate table. -/
  monomialToSource : Fin 8 → Coordinates 8
  /-- Source coordinates of the independently fixed requested expression. -/
  sourceRequest : Coordinates 8

/-- The exact source and destination obligations consumed by kernel replay.
All fields, including the requested expression, have fixed external meanings. -/
def AcceptsExchange (incoming : Exchange) : Prop :=
  (incoming.sourceRows = pushforwardRows ∧
    incoming.sourceToMonomial = pushforwardToMonomial ∧
    incoming.monomialToSource = monomialToPushforward ∧
    incoming.sourceRequest = requestedPushforward) ∧
      AcceptsPresentation columns rows requested incoming.presentation

/-- Bind every source conversion field as well as the semantic destination
frame and exact requested expression. Hashes alone are not proof checks. -/
def checkExchange (incoming : Exchange) : Bool :=
  decide (incoming.sourceRows = pushforwardRows ∧
    incoming.sourceToMonomial = pushforwardToMonomial ∧
    incoming.monomialToSource = monomialToPushforward ∧
    incoming.sourceRequest = requestedPushforward) &&
      checkPresentation columns rows requested incoming.presentation

/-- A successful exchange matches both coordinate systems and checks the
fixed claim. The external data cannot replace a source table or request. -/
theorem checkExchange_eq_true_iff (incoming : Exchange) :
    checkExchange incoming = true ↔
      (incoming.sourceRows = pushforwardRows ∧
        incoming.sourceToMonomial = pushforwardToMonomial ∧
        incoming.monomialToSource = monomialToPushforward ∧
        incoming.sourceRequest = requestedPushforward) ∧
          checkPresentation columns rows requested incoming.presentation = true := by
  rw [checkExchange, Bool.and_eq_true, decide_eq_true_eq]

/-- Proof replay has precisely the Boolean exchange checker's conditions. -/
theorem checkExchange_eq_true_iff_accepts (incoming : Exchange) :
    checkExchange incoming = true ↔ AcceptsExchange incoming := by
  rw [checkExchange_eq_true_iff, AcceptsExchange,
    checkPresentation_eq_true_iff_accepts]

/-- Direct checked fields and arithmetic prove the fixed formal consequence. -/
theorem acceptsExchange_sound (incoming : Exchange) (h : AcceptsExchange incoming) :
    interpret columns requested ∈ relationSpan columns rows :=
  acceptsPresentation_sound columns rows requested incoming.presentation h.2

/-- Accepted exchange data prove the independently fixed formal relation
consequence. Geometric vanishing of the generator rows remains an input. -/
theorem checkExchange_sound (incoming : Exchange) (h : checkExchange incoming = true) :
    interpret columns requested ∈ relationSpan columns rows :=
  checkPresentation_sound columns rows requested incoming.presentation
    ((checkExchange_eq_true_iff incoming).1 h).2

end AxiomaticGW.AdmcyclesGenusTwo
