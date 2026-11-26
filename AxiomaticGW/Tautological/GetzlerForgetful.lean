/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GetzlerAncestors
public import AxiomaticGW.Tautological.GluingForgetful

/-!
# Getzler ancestor equations with arbitrary additional markings

The original checked four-marking relation is pulled back through any finite
sequence of forgetful maps. Its raw graph expansion is proved by elementary
gluing base change. Arbitrary ancestor powers and states are then inserted on
the larger moduli space, so no decorated forgetful formula is presumed.

The original relation, coefficients, request, and searched witness are
unchanged. Each added marking is placed on every vertex, with repetitions
retained. This supplies equations, not a solved reconstruction recurrence or
a comparison with stable-map descendants.
-/

@[expose] public section

namespace AxiomaticGW.GetzlerGraphs

/-- The 25 tree columns have three vertices; the eight cyclic columns have two. -/
theorem expression_vertexCount (i : Fin 33) :
    (expression i).graph.graph.vertexCount = if i.val < 25 then 3 else 2 := by
  fin_cases i <;> rfl

/-- Exact number of raw placements, before identifying coincident graph classes. -/
theorem sum_length_addMarkings (n : ℕ) :
    (∑ i : Fin 33, ((expression i).addMarkings n).length) = 25 * 3 ^ n + 8 * 2 ^ n := by
  simp only [GluingExpression.length_addMarkings, expression_vertexCount]
  norm_num [Fin.sum_univ_succ]
  ring

universe u

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

attribute [local instance] strataRealizationModule

/-- Sum the actual full-class ancestor contractions over every marking placement. -/
noncomputable def gwAncestorChannelWithMarkings (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (n : ℕ) (beta : B)
    (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V) (i : Fin 33) : R :=
  (((expression i).addMarkings n).map fun z ↦ z.gwAncestorContraction Omega P I beta k a).sum

/-- Adding no markings recovers the earlier four-marking ancestor channel. -/
theorem gwAncestorChannelWithMarkings_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (beta : B)
    (k : Fin 4 → ℕ) (a : Fin 4 → V) (i : Fin 33) :
    gwAncestorChannelWithMarkings Omega P I 0 beta k a i =
      gwAncestorChannel Omega P I beta k a i := by
  simp only [gwAncestorChannelWithMarkings, GluingExpression.addMarkings,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, gwAncestorChannel]

variable (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (expression i).Compatible A F N)

include H hsource

/-- The forgetful pullback of each held column is its derived sum of contractions. -/
theorem integrate_column_with_markings (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V)
    (i : Fin 33) :
    (A 1 (Fin 4)).integrateForgetExtra I stableArity n
      (P.monomial 1 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) k *
        Omega.omega 1 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) beta a)
      (StrataModule.basis (columns i)) =
      gwAncestorChannelWithMarkings Omega P I n beta k a i := by
  rw [← expression_stratum i,
    (expression i).integrateForgetExtra_eq_sum A F N H n (hsource i) (houtput i)]
  unfold gwAncestorChannelWithMarkings
  congr 1
  apply List.map_congr_left
  intro z hz
  rw [← z.gwAncestorIntegral_apply A Omega P I beta k a]
  exact congrArg (fun f ↦ f a)
    (z.gwAncestorIntegral_eq_contraction A F N Omega P (houtput i z hz) beta k)

variable (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)

include G hcycle

/-- The same exact certificate gives the ancestor equation after any finite
number of additional markings, using only the stated geometric inputs. -/
theorem certificate_ancestor_with_markings_eq_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V)
    (c : RelationCertificate.Certificate 1)
    (hcheck : RelationCertificate.check rows requested c = true) :
    (∑ i, algebraMap ℚ R (requested i) *
      gwAncestorChannelWithMarkings Omega P I n beta k a i) = 0 := by
  let w := P.monomial 1 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) k *
    Omega.omega 1 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n) beta a
  have h : (A 1 (Fin 4)).integrateForgetExtra I stableArity n w
      (RelationCertificate.interpret columns requested) = 0 := by
    apply RelationCertificate.evaluation_eq_zero columns rows requested c hcheck
    intro r
    rw [StrataRealization.integrateForgetExtra_apply]
    change I.integrate 1 (ExtraMarkings n (Fin 4)) (stableArity.extraMarkings n)
      (w * C.forgetExtra 1 (Fin 4) stableArity n
        ((A 1 (Fin 4)).map (RelationCertificate.interpret columns row))) = 0
    rw [map_row_eq_zero (A 1 (Fin 4)) G hcycle, map_zero, mul_zero, map_zero]
  rw [RelationCertificate.interpret_apply, map_sum] at h
  dsimp only [w] at h
  simpa only [map_smul, Algebra.smul_def,
    integrate_column_with_markings A F N H hsource Omega P n houtput beta k a] using h

/-- Actual incoming replay remains bound to the original marked request
before the proved forgetful operation and ancestor evaluation are applied. -/
theorem exchange_ancestor_with_markings_eq_zero (Omega : GromovWittenTheory R V B D C)
    (P : PsiClasses C) (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 4) → ℕ) (a : ExtraMarkings n (Fin 4) → V)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (hp : AcceptsExchange p) :
    (∑ i, algebraMap ℚ R (requested i) *
      gwAncestorChannelWithMarkings Omega P I n beta k a i) = 0 :=
  certificate_ancestor_with_markings_eq_zero A F N H hsource G hcycle Omega P n houtput beta k a
    p.certificate ((RelationCertificate.check_eq_true_iff _ _ _).mpr hp.2)

end AxiomaticGW.GetzlerGraphs
