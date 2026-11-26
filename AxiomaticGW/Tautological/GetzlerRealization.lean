/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GetzlerGraphs
public import AxiomaticGW.Tautological.LegPsiRealization
public import AxiomaticGW.GW.Descendants.Basic

/-!
# Realization of the expanded Getzler certificate

The graph frame and normalization are fixed independently of replay data.
The geometric input is the pre-existing GetzlerRelationGeometry class relation
and identification of its seven normalized cycles. Kernel arithmetic derives
the held delta23 consequence and its integrals against arbitrary classes.

This does not construct geometric gluing maps or identify the 33 integrals
with iterated GW contractions. That identification is a separate obligation;
the ancestor specialization below uses the actual GW class family.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

open scoped BigOperators

/-- Kernel witness for the held delta23 consequence. Exported witnesses must
still satisfy the same held-coordinate equation. -/
def certificate : RelationCertificate.Certificate 1 := ⟨fun _ ↦ -1 / 4⟩

/-- Exact arithmetic verifies the independently fixed claim in the expanded frame. -/
theorem check_requested : RelationCertificate.check rows requested certificate = true := by
  rw [RelationCertificate.check_eq_true_iff]
  funext i
  fin_cases i <;>
    norm_num [RelationCertificate.combination, certificate, rows, row, requested,
      kind, normalization, GetzlerStratum.coefficient, Fin.sum_univ_one]

/-- The original raw relation is nonzero before a geometric relation is imposed. -/
theorem row_ne_zero : RelationCertificate.interpret columns row ≠ 0 := by
  intro h
  have hi := congrArg (fun r ↦ r (columns 0)) h
  rw [RelationCertificate.interpret_apply_column columns columns_injective] at hi
  norm_num [row, kind, normalization] at hi

/-- The held request is a genuine nonzero formal consequence. -/
theorem requested_ne_zero : RelationCertificate.interpret columns requested ≠ 0 := by
  intro h
  have hi := congrArg (fun r ↦ r (columns 0)) h
  rw [RelationCertificate.interpret_apply_column columns columns_injective] at hi
  norm_num [requested, kind, normalization] at hi

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} (A : StrataRealization C 1 (Fin 4))
  (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, A.map (cycle x) = G.cycle x)

attribute [local instance] strataRealizationModule

include G hcycle

/-- The explicit raw graph row vanishes by the named geometric class relation,
not by an assumed numerical reconstruction equation. -/
theorem map_row_eq_zero : A.map (RelationCertificate.interpret columns row) = 0 := by
  rw [← encoding_relation_eq]
  exact (A.mem_kernel_iff _).mp (encoding.relation_mem_realization_kernel A G hcycle)

/-- Every checked certificate yields a zero integral against the held class. -/
theorem certificate_integral_eq_zero (I : StableCurveIntegration C)
    (w : C.H 1 (Fin 4)) (c : RelationCertificate.Certificate 1)
    (hcheck : RelationCertificate.check rows requested c = true) :
    A.integrateAgainst I stableArity w
      (RelationCertificate.interpret columns requested) = 0 := by
  apply RelationCertificate.evaluation_eq_zero columns rows requested c hcheck
  intro r
  rw [StrataRealization.integrateAgainst_apply]
  change I.integrate 1 (Fin 4) stableArity
    (w * A.map (RelationCertificate.interpret columns row)) = 0
  rw [map_row_eq_zero A G hcycle, mul_zero, map_zero]

/-- Accepted exchange data certifies precisely the caller's fixed integral. -/
theorem exchange_integral_eq_zero (I : StableCurveIntegration C)
    (w : C.H 1 (Fin 4)) (p : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hp : AcceptsExchange p) :
    A.integrateAgainst I stableArity w
      (RelationCertificate.interpret columns requested) = 0 :=
  certificate_integral_eq_zero A G hcycle I w p.certificate
    ((RelationCertificate.check_eq_true_iff _ _ _).mpr hp.2)

/-- The expanded scalar equation retains each of the 33 labelled raw integrals. -/
theorem certificate_integral_sum_eq_zero (I : StableCurveIntegration C)
    (w : C.H 1 (Fin 4)) (c : RelationCertificate.Certificate 1)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, algebraMap ℚ R (requested i) *
      A.integrateAgainst I stableArity w (StrataModule.basis (columns i))) = 0 := by
  have h := certificate_integral_eq_zero A G hcycle I w c hcheck
  rw [RelationCertificate.interpret_apply, map_sum] at h
  simpa only [map_smul, Algebra.smul_def] using h

variable {V B : Type u} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCancelCommMonoid B]
  {D : EffectiveCurveMonoid B}

/-- Actual GW classes with arbitrary external ancestor powers can be paired
with the expanded relation. Class-to-contraction evaluation is still separate. -/
theorem ancestor_integral_sum_eq_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (beta : B)
    (k : Fin 4 → ℕ) (a : Fin 4 → V)
    (c : RelationCertificate.Certificate 1)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, algebraMap ℚ R (requested i) *
      A.integrateAgainst I stableArity
        (P.monomial 1 (Fin 4) stableArity k * Omega.omega 1 (Fin 4) stableArity beta a)
        (StrataModule.basis (columns i))) = 0 :=
  certificate_integral_sum_eq_zero A G hcycle I _ c hcheck

end AxiomaticGW.GetzlerGraphs
