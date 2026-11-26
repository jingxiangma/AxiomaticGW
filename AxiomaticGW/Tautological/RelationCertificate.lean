/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.StrataModule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Exact certificates for finite relation combinations

The caller fixes the graph columns, relation rows, and requested expression.
A certificate supplies only rational row coefficients. Kernel evaluation of
`check` proves formal relation-span membership for that exact request.
Vanishing after a realization requires the stated generator hypotheses;
neither the checker nor a formal quotient proves those geometric inputs.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

namespace RelationCertificate

universe u

/-- Rational coordinates relative to a fixed ordered graph list. -/
abbrev Coordinates (n : ℕ) := Fin n → ℚ

/-- Coefficients for every row in the caller's fixed relation system. -/
structure Certificate (m : ℕ) where
  /-- Exact rational row coefficients; no requested claim is supplied here. -/
  weights : Fin m → ℚ

/-- Candidate exchange data. Graph meanings, graph normalization factors,
and relation rows are checked against the caller's fixed raw system. -/
structure Presentation (g : ℕ) (S : Type) [Fintype S] (m n : ℕ) where
  /-- Candidate semantic graph columns, with their original external labels. -/
  columns : Fin n → TautologicalStratum g S
  /-- Factor multiplying each raw gluing-pushforward graph column. -/
  columnFactors : Coordinates n
  /-- Candidate relation rows in those coordinates. -/
  rows : Fin m → Coordinates n
  /-- The expression claimed by the incoming exchange data. -/
  claimedRequest : Coordinates n
  /-- The proposed exact row combination. -/
  certificate : Certificate m

/-- The certificate's rational combination in the fixed coordinates. -/
def combination {m n : ℕ} (rows : Fin m → Coordinates n)
    (certificate : Certificate m) : Coordinates n :=
  fun column ↦ ∑ row, certificate.weights row * rows row column

/-- Coordinatewise evaluation is the usual finite linear combination. The
explicit scalar sums also support direct kernel arithmetic reduction. -/
theorem combination_eq_sum {m n : ℕ} (rows : Fin m → Coordinates n)
    (certificate : Certificate m) :
    combination rows certificate = ∑ row, certificate.weights row • rows row := by
  funext column
  simp only [combination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The standard finite linear-combination map admits the explicit
coordinatewise evaluation form. -/
theorem linearCombination_eq_combination {m n : ℕ} (rows : Fin m → Coordinates n)
    (weights : Fin m → ℚ) :
    Fintype.linearCombination ℚ rows weights = combination rows ⟨weights⟩ :=
  (combination_eq_sum rows ⟨weights⟩).symm

/-- Check the exact requested coordinate expression against the fixed rows. -/
def check {m n : ℕ} (rows : Fin m → Coordinates n) (requested : Coordinates n)
    (certificate : Certificate m) : Bool :=
  decide (combination rows certificate = requested)

/-- A successful Boolean check supplies the complete coordinate equality. -/
theorem check_eq_true_iff {m n : ℕ} (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (certificate : Certificate m) :
    check rows requested certificate = true ↔ combination rows certificate = requested := by
  rw [check, decide_eq_true_eq]

/-- Reject changed graph columns, normalization factors, or relation rows
before checking the witness for the caller's exact requested expression. -/
def checkPresentation {g m n : ℕ} {S : Type} [Fintype S]
    [DecidableEq (TautologicalStratum g S)]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (presentation : Presentation g S m n) : Bool :=
  decide (presentation.columns = columns ∧
    presentation.columnFactors = 1 ∧ presentation.rows = rows ∧
      presentation.claimedRequest = requested) &&
      check rows requested presentation.certificate

/-- Every supplied exchange field is bound to the fixed raw relation system
by a successful presentation check. The request remains a caller argument. -/
theorem checkPresentation_eq_true_iff {g m n : ℕ} {S : Type} [Fintype S]
    [DecidableEq (TautologicalStratum g S)]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (presentation : Presentation g S m n) :
    checkPresentation columns rows requested presentation = true ↔
      (presentation.columns = columns ∧ presentation.columnFactors = 1 ∧
        presentation.rows = rows ∧ presentation.claimedRequest = requested) ∧
          check rows requested presentation.certificate = true := by
  rw [checkPresentation, Bool.and_eq_true, decide_eq_true_eq]

/-- Kernel replay may supply field equalities and rational arithmetic
directly. This predicate has exactly the Boolean checker's acceptance
conditions, including the caller's independent requested expression. -/
def AcceptsPresentation {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (presentation : Presentation g S m n) : Prop :=
  (presentation.columns = columns ∧ presentation.columnFactors = 1 ∧
    presentation.rows = rows ∧ presentation.claimedRequest = requested) ∧
      combination rows presentation.certificate = requested

/-- Direct proof replay and Boolean acceptance have identical meanings. -/
theorem checkPresentation_eq_true_iff_accepts {g m n : ℕ} {S : Type} [Fintype S]
    [DecidableEq (TautologicalStratum g S)]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (presentation : Presentation g S m n) :
    checkPresentation columns rows requested presentation = true ↔
      AcceptsPresentation columns rows requested presentation := by
  rw [checkPresentation_eq_true_iff, AcceptsPresentation, check_eq_true_iff]

/-- Interpret coordinates in the existing free strata module. Columns need
not be independent for soundness; the caller fixes their semantic meanings. -/
noncomputable def interpret {g n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) :
    Coordinates n →ₗ[ℚ] StrataModule g S :=
  Fintype.linearCombination ℚ (fun i ↦ StrataModule.basis (columns i))

/-- The formal meaning of a coordinate vector is its basis combination. -/
theorem interpret_apply {g n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (x : Coordinates n) :
    interpret columns x = ∑ i, x i • StrataModule.basis (columns i) := rfl

/-- Distinct columns recover each coordinate by evaluation in the free
strata module. This ties coordinate requests to their formal expressions. -/
theorem interpret_apply_column {g n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (hcolumns : Function.Injective columns)
    (x : Coordinates n) (i : Fin n) : interpret columns x (columns i) = x i := by
  classical
  simp only [interpret_apply, Finset.sum_apply', Finsupp.smul_apply, StrataModule.basis,
    Finsupp.single_apply, hcolumns.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Coordinates in distinct graph columns determine the formal expression
faithfully; no equality of different requests is silently identified. -/
theorem interpret_injective {g n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (hcolumns : Function.Injective columns) :
    Function.Injective (interpret columns) := by
  intro x y h
  funext i
  have hi := congrArg (fun z : StrataModule g S ↦ z (columns i)) h
  simpa only [interpret_apply_column columns hcolumns] using hi

/-- Columns of one codimension give homogeneous coordinate expressions. -/
theorem interpret_mem_degree {g n d : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S)
    (hcolumns : ∀ i, (columns i).codimension = d) (x : Coordinates n) :
    interpret columns x ∈ StrataModule.degree d := by
  rw [interpret_apply]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [← hcolumns i]
  exact StrataModule.basis_mem_degree (columns i)

/-- Coordinate combinations preserve their meaning in the strata module. -/
theorem interpret_combination {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (certificate : Certificate m) :
    interpret columns (combination rows certificate) =
      ∑ row, certificate.weights row • interpret columns (rows row) := by
  simp only [combination_eq_sum, map_sum, map_smul]

/-- The explicitly supplied formal relation span. No completeness or
geometric validity of this system is assumed by the definition. -/
noncomputable def relationSpan {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n) :
    Submodule ℚ (StrataModule g S) :=
  Submodule.span ℚ (Set.range fun row ↦ interpret columns (rows row))

/-- Every explicit row combination belongs to the supplied formal span. -/
theorem combination_mem_relationSpan {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (certificate : Certificate m) :
    interpret columns (combination rows certificate) ∈ relationSpan columns rows := by
  rw [interpret_combination]
  apply Submodule.sum_mem
  intro row _
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self row)

/-- Kernel-checked equality proves membership in the fixed formal span. -/
theorem check_sound {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (certificate : Certificate m)
    (h : check rows requested certificate = true) :
    interpret columns requested ∈ relationSpan columns rows := by
  rw [← (check_eq_true_iff rows requested certificate).1 h]
  exact combination_mem_relationSpan columns rows certificate

/-- Direct field and arithmetic proofs certify the same fixed formal claim,
without computing quotient equality inside a closed Boolean proof term. -/
theorem acceptsPresentation_sound {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (presentation : Presentation g S m n)
    (h : AcceptsPresentation columns rows requested presentation) :
    interpret columns requested ∈ relationSpan columns rows := by
  rw [← h.2]
  exact combination_mem_relationSpan columns rows presentation.certificate

/-- A checked presentation certifies the caller's fixed formal claim. -/
theorem checkPresentation_sound {g m n : ℕ} {S : Type} [Fintype S]
    [DecidableEq (TautologicalStratum g S)]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (presentation : Presentation g S m n)
    (h : checkPresentation columns rows requested presentation = true) :
    interpret columns requested ∈ relationSpan columns rows :=
  check_sound columns rows requested presentation.certificate
    ((checkPresentation_eq_true_iff columns rows requested presentation).1 h).2

/-- The accepted request vanishes in the quotient imposing the fixed rows. -/
theorem quotient_eq_zero {g m n : ℕ} {S : Type} [Fintype S]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (certificate : Certificate m)
    (h : check rows requested certificate = true) :
    StrataModule.quotientMk (relationSpan columns rows)
      (interpret columns requested) = 0 :=
  StrataModule.quotientMk_eq_zero _ (check_sound columns rows requested certificate h)

/-- A checked request vanishes under a linear evaluation only when every
fixed relation row is proved to vanish under that same evaluation. -/
theorem evaluation_eq_zero {g m n : ℕ} {S : Type} {M : Type u} [Fintype S]
    [AddCommMonoid M] [Module ℚ M]
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (certificate : Certificate m)
    (h : check rows requested certificate = true)
    (evaluation : StrataModule g S →ₗ[ℚ] M)
    (hrows : ∀ row, evaluation (interpret columns (rows row)) = 0) :
    evaluation (interpret columns requested) = 0 := by
  rw [← (check_eq_true_iff rows requested certificate).1 h, interpret_combination]
  simp only [map_sum, map_smul, hrows, smul_zero, Finset.sum_const_zero]

end RelationCertificate

end AxiomaticGW
