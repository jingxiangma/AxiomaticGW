/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

import AxiomaticGWTest.Tautological.AdmcyclesReplay
import AxiomaticGW.Tautological.StrataRealization
import AxiomaticGW.Tautological.GraphIsomorphisms

set_option linter.privateModule false

/-!
# Exact relation certificate regressions

These tests hold the requested formal claim fixed while changing candidate
fields. A checked relation consequence is nonzero in the free strata module;
its geometric vanishing still needs the explicit generator hypotheses.
-/

namespace AxiomaticGWTest.Tautological.RelationCertificate

open AxiomaticGW RelationCertificate AdmcyclesGenusTwo

private abbrev candidate := AdmcyclesGenusTwoReplay.presentation

/-- The accepted request is a homogeneous codimension-two expression. -/
example : interpret columns requested ∈ StrataModule.degree 2 :=
  interpret_mem_degree columns columns_codimension requested

/-- The searched consequence is nonzero before imposing relation rows. -/
example : interpret columns requested ≠ 0 := by
  intro h
  have hc := congrArg (fun x : StrataModule 2 (Fin 0) ↦ x (columns 1)) h
  simp only [interpret_apply_column columns columns_injective, Finsupp.zero_apply] at hc
  norm_num only [requested, Matrix.cons_val_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] at hc

/-- A zero row witness cannot certify this nonzero requested expression. -/
example : check rows requested (⟨0⟩ : Certificate 7) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hc := congrFun ((check_eq_true_iff rows requested ⟨0⟩).1 h) 1
  norm_num only [combination, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    requested, Matrix.cons_val_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hc

/-- Dividing an incoming raw column by an automorphism factor is rejected. -/
example : checkPresentation columns rows requested
    { candidate with columnFactors := fun _ ↦ (1 / 2 : ℚ) } = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hf := ((checkPresentation_eq_true_iff _ _ _ _).1 h).1.2.1
  have hc := congrFun hf 0
  norm_num only [Pi.one_apply] at hc

/-- A changed graph meaning in the same column slot is rejected. -/
example : checkPresentation columns rows requested
    { candidate with columns := Function.update columns 2 (columns 3) } = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hg := ((checkPresentation_eq_true_iff _ _ _ _).1 h).1.1
  have hc := congrFun hg 2
  change Function.update columns 2 (columns 3) 2 = columns 2 at hc
  rw [Function.update_self] at hc
  exact (by decide : (3 : Fin 8) ≠ 2) (columns_injective hc)

/-- Row numbers refer to the fixed system, even when each row is legitimate. -/
example : checkPresentation columns rows requested
    { candidate with rows := Function.update rows 0 (rows 3) } = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hr := ((checkPresentation_eq_true_iff _ _ _ _).1 h).1.2.2.1
  have hc := congrArg (fun x : Fin 7 → Coordinates 8 ↦ x 0 1) hr
  simp only [Function.update_self] at hc
  norm_num only [rows, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] at hc

/-- The candidate cannot choose a different requested expression. -/
example : checkPresentation columns rows requested
    { candidate with claimedRequest := 0 } = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hr := ((checkPresentation_eq_true_iff _ _ _ _).1 h).1.2.2.2
  have hc := congrFun hr 1
  norm_num only [Pi.zero_apply, requested, Matrix.cons_val_one, Matrix.cons_val_zero',
    Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one] at hc

/-- Acceptance of the original claim cannot be reused for a caller's new claim. -/
example : checkPresentation columns rows (0 : Coordinates 8) candidate = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hr := ((checkPresentation_eq_true_iff _ _ _ _).1 h).1.2.2.2
  have hc := congrFun hr 1
  norm_num only [candidate, AdmcyclesGenusTwoReplay.presentation, Pi.zero_apply,
    Matrix.cons_val_one,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hc

/-- Source coordinate conversion is checked, rather than merely carried. -/
example : checkExchange { AdmcyclesGenusTwoReplay.incoming with
    sourceToMonomial := 0 } = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hd := ((checkExchange_eq_true_iff _).1 h).1.2.1
  have hc := congrArg (fun x : Fin 8 → Coordinates 8 ↦ x 0 0) hd
  norm_num only [Pi.zero_apply, pushforwardToMonomial, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hc

/-- Empty row systems certify zero without an arbitrary seed or relation. -/
example : check (Fin.elim0 : Fin 0 → Coordinates 1) 0 ⟨Fin.elim0⟩ = true := by
  rw [check_eq_true_iff]
  funext i
  simp only [combination, Fintype.sum_empty, Pi.zero_apply]

/-- An empty relation system cannot certify a nonzero coordinate. -/
example : check (Fin.elim0 : Fin 0 → Coordinates 1) (fun _ ↦ 1) ⟨Fin.elim0⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hc := congrFun ((check_eq_true_iff _ _ _).1 h) 0
  norm_num only [combination, Fintype.sum_empty] at hc

/-- Decoration stabilizers agree with the source's loop conventions; the
raw column factors stay one regardless of these automorphism orders. -/
example :
    (DecoratedStableGraph.toDecoration graph4Candidate graph4Valid
      graph4Exponents).automorphismCount = 2 ∧
    (DecoratedStableGraph.toDecoration graph5Candidate graph5Valid
      graph5Exponents).automorphismCount = 1 ∧
    (DecoratedStableGraph.toDecoration graph7Candidate graph7Valid
      graph7Exponents).automorphismCount = 8 := by
  simp only [DecoratedStableGraph.toDecoration_eq_mk]
  decide

universe u

attribute [local instance] strataRealizationModule

/-- The existing cohomological realization consumes the certificate only
with explicit vanishing proofs for each source row. -/
example {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) (A : StrataRealization C 2 (Fin 0))
    (hrows : ∀ row, A.map (interpret columns (rows row)) = 0) :
    A.map (interpret columns requested) = 0 := by
  have hp := AdmcyclesGenusTwoReplay.accepted.2
  have hc := (check_eq_true_iff _ _ _).2 hp.2
  exact evaluation_eq_zero columns rows requested _ hc A.map hrows

end AxiomaticGWTest.Tautological.RelationCertificate
