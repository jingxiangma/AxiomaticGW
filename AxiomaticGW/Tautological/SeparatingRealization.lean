/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.SeparatingGluing
public import AxiomaticGW.Tautological.LegPsiRealization
public import AxiomaticGW.GW.SeparatingBoundary

/-!
# Realization and certificate transfer through separating gluing

Raw graph-map composition is a primitive compatibility on pairs of basis
strata. Bilinearity extends it to arbitrary combinations. Relations in
either component then remain geometric relations, even when their glued
graphs lie below the dimension bound of the whole target space.

The CohFT and full-curve-class GW boundary functionals evaluate the actual
graph operation. No final numerical recurrence or imported relation validity
is assumed by the compatibility definition.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace RelationCertificate

/-- A fixed right stratum glues every coordinate of the left expression.
Coincident output columns combine in the free module. -/
theorem separating_left_interpret {g₁ g₂ m : ℕ} {S T : Type}
    [Fintype S] [Fintype T]
    (columns : Fin m → TautologicalStratum g₁ (Option S)) (x : Coordinates m)
    (y : TautologicalStratum g₂ (Option T)) :
    StrataModule.separating (interpret columns x) (StrataModule.basis y) =
      interpret (fun i ↦ (columns i).separating y) x := by
  simp only [interpret_apply, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, StrataModule.separating_basis_basis]

/-- A fixed left stratum glues every coordinate of the right expression. -/
theorem separating_right_interpret {g₁ g₂ m : ℕ} {S T : Type}
    [Fintype S] [Fintype T]
    (x : TautologicalStratum g₁ (Option S))
    (columns : Fin m → TautologicalStratum g₂ (Option T)) (y : Coordinates m) :
    StrataModule.separating (StrataModule.basis x) (interpret columns y) =
      interpret (fun i ↦ x.separating (columns i)) y := by
  simp only [interpret_apply, map_sum, map_smul, StrataModule.separating_basis_basis]

end RelationCertificate

namespace StrataRealization

universe u

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
  {g₁ g₂ : ℕ} {S T : Type} [Fintype S] [Fintype T]

attribute [local instance] strataRealizationModule

/-- Composing the two raw graph maps with elementary separating gluing is
a cohomology law, independent of any CohFT, GW family, or relation. -/
def SeparatingCompatible (A : StrataRealization C g₁ (Option S))
    (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T))
    (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T)) : Prop :=
  ∀ x y, U.map (StrataModule.basis (x.separating y)) =
    F.push g₁ g₂ S T h₁ h₂
      (A.map (StrataModule.basis x) ⊗ₜ[R] B.map (StrataModule.basis y))

/-- Primitive composition extends bilinearly to all rational combinations. -/
theorem map_separating (A : StrataRealization C g₁ (Option S))
    (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂)
    (r : StrataModule g₁ (Option S)) (s : StrataModule g₂ (Option T)) :
    U.map (StrataModule.separating r s) =
      F.push g₁ g₂ S T h₁ h₂ (A.map r ⊗ₜ[R] B.map s) := by
  induction r using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, zero_tmul]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, add_tmul, ha, hb]
  | single x q =>
    induction s using Finsupp.induction_linear with
    | zero => simp only [map_zero, tmul_zero]
    | add a b ha hb => simp only [map_add, tmul_add, ha, hb]
    | single y p =>
      have hx : Finsupp.single x q = q • StrataModule.basis x := by
        simp only [StrataModule.basis, Finsupp.smul_single, smul_eq_mul, mul_one]
      have hy : Finsupp.single y p = p • StrataModule.basis y := by
        simp only [StrataModule.basis, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [StrataModule.separating_single_single, map_smul, hAB x y]
      rw [hx, hy, map_smul, map_smul]
      change (algebraMap ℚ R (q * p)) • F.push g₁ g₂ S T h₁ h₂
        (A.map (StrataModule.basis x) ⊗ₜ[R] B.map (StrataModule.basis y)) =
          F.push g₁ g₂ S T h₁ h₂
            (((algebraMap ℚ R q) • A.map (StrataModule.basis x)) ⊗ₜ[R]
              ((algebraMap ℚ R p) • B.map (StrataModule.basis y)))
      rw [smul_tmul_smul, map_smul, map_mul]

/-- Any left geometric relation remains a relation after raw gluing with
an arbitrary right combination. No target dimension test is substituted. -/
theorem separating_left_mem_kernel (A : StrataRealization C g₁ (Option S))
    (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂)
    {r : StrataModule g₁ (Option S)} (hr : r ∈ A.kernel)
    (s : StrataModule g₂ (Option T)) : StrataModule.separating r s ∈ U.kernel := by
  rw [U.mem_kernel_iff, A.map_separating B U F h₁ h₂ hAB,
    (A.mem_kernel_iff r).mp hr, zero_tmul, map_zero]

/-- The same geometric preservation holds for a relation in the right
component and arbitrary left data. -/
theorem separating_right_mem_kernel (A : StrataRealization C g₁ (Option S))
    (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂)
    (r : StrataModule g₁ (Option S)) {s : StrataModule g₂ (Option T)}
    (hs : s ∈ B.kernel) : StrataModule.separating r s ∈ U.kernel := by
  rw [U.mem_kernel_iff, A.map_separating B U F h₁ h₂ hAB,
    (B.mem_kernel_iff s).mp hs, tmul_zero, map_zero]

/-- The integrated explicit graph operation evaluates the pullback of the
held upper insertion on the product of the component realizations. -/
theorem integrateAgainst_separating (A : StrataRealization C g₁ (Option S))
    (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂)
    (w : C.H (g₁ + g₂) (S ⊕ T))
    (r : StrataModule g₁ (Option S)) (s : StrataModule g₂ (Option T)) :
    U.integrateAgainst I (StableArity.separating h₁ h₂) w (StrataModule.separating r s) =
      I.tensorIntegral g₁ g₂ (Option S) (Option T) h₁ h₂
        (C.separating g₁ g₂ S T h₁ h₂ w * (A.map r ⊗ₜ[R] B.map s)) := by
  rw [integrateAgainst_apply, A.map_separating B U F h₁ h₂ hAB, F.integrate_mul_push]

/-- The explicit graph operation uses the actual CohFT boundary functional. -/
theorem integrateAgainst_separating_cohFT {V : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (A : StrataRealization C g₁ (Option S)) (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂) (Omega : CohFT R V C)
    (a : S ⊕ T → V) (r : StrataModule g₁ (Option S)) (s : StrataModule g₂ (Option T)) :
    U.integrateAgainst I (StableArity.separating h₁ h₂)
        (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) a)
        (StrataModule.separating r s) =
      Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ (A.map r ⊗ₜ[R] B.map s) a := by
  rw [integrateAgainst_apply, A.map_separating B U F h₁ h₂ hAB,
    CohFT.separatingInvariant_apply]

/-- Class-resolved GW evaluation of the graph operation uses the derived
boundary functional, hence the convolution over all effective splittings. -/
theorem integrateAgainst_separating_gw {V Bclass : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid Bclass] {D : EffectiveCurveMonoid Bclass}
    (A : StrataRealization C g₁ (Option S)) (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂) (Omega : GromovWittenTheory R V Bclass D C)
    (beta : Bclass) (a : S ⊕ T → V)
    (r : StrataModule g₁ (Option S)) (s : StrataModule g₂ (Option T)) :
    U.integrateAgainst I (StableArity.separating h₁ h₂)
        (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) beta a)
        (StrataModule.separating r s) =
      Omega.separatingInvariant F g₁ g₂ S T h₁ h₂ beta (A.map r ⊗ₜ[R] B.map s) a := by
  rw [integrateAgainst_apply, A.map_separating B U F h₁ h₂ hAB,
    GromovWittenTheory.separatingInvariant_apply]

/-- Gluing two normalized fundamental strata with arbitrary source psi
monomials gives the full-class convolution of the existing GW ancestors.
The two distinguished source powers become the new node decorations. -/
theorem integrateAgainst_separating_fundamental_gw {V Bclass : Type u}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid Bclass] {D : EffectiveCurveMonoid Bclass}
    (A : StrataRealization C g₁ (Option S)) (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (P : PsiClasses C)
    (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂)
    (hA : A.LegPsiCompatible P h₁) (hB : B.LegPsiCompatible P h₂)
    (hfundA : A.map (StrataModule.basis
      (TautologicalStratum.fundamental g₁ (Option S) h₁)) = 1)
    (hfundB : B.map (StrataModule.basis
      (TautologicalStratum.fundamental g₂ (Option T) h₂)) = 1)
    (Omega : GromovWittenTheory R V Bclass D C) (beta : Bclass)
    (a : S ⊕ T → V) (k : Option S → ℕ) (l : Option T → ℕ) :
    U.integrateAgainst I (StableArity.separating h₁ h₂)
        (Omega.omega (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂) beta a)
        (StrataModule.separating
          (StrataModule.mulLegPsi k (StrataModule.basis
            (TautologicalStratum.fundamental g₁ (Option S) h₁)))
          (StrataModule.mulLegPsi l (StrataModule.basis
            (TautologicalStratum.fundamental g₂ (Option T) h₂)))) =
      ∑ split ∈ D.splittings beta,
        Omega.pairing.pairContract
          (Omega.ancestorInvariant P I g₁ (Option S) h₁ split.1 k)
          (Omega.ancestorInvariant P I g₂ (Option T) h₂ split.2 l) a := by
  rw [A.integrateAgainst_separating_gw B U F h₁ h₂ hAB,
    A.map_mulLegPsi P h₁ hA, B.map_mulLegPsi P h₂ hB,
    hfundA, hfundB, one_mul, one_mul, Omega.separatingInvariant_monomial]
  simp only [sum_apply]

/-- An exact original left-row certificate transfers to its expanded
integrated glued equation with a held right graph and upper insertion. -/
theorem certificate_separating_left_eq_zero {m n : ℕ}
    (A : StrataRealization C g₁ (Option S)) (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂) (w : C.H (g₁ + g₂) (S ⊕ T))
    (columns : Fin n → TautologicalStratum g₁ (Option S))
    (rows : Fin m → RelationCertificate.Coordinates n)
    (requested : RelationCertificate.Coordinates n)
    (certificate : RelationCertificate.Certificate m)
    (hcheck : RelationCertificate.check rows requested certificate = true)
    (hrows : ∀ row, A.map (RelationCertificate.interpret columns (rows row)) = 0)
    (y : TautologicalStratum g₂ (Option T)) :
    (∑ i, requested i • I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
      (w * U.map (StrataModule.basis ((columns i).separating y)))) = 0 := by
  have hz := RelationCertificate.evaluation_eq_zero columns rows requested certificate hcheck
    ((U.integrateAgainst I (StableArity.separating h₁ h₂) w).comp
      (StrataModule.separating.flip (StrataModule.basis y))) (by
        intro row
        rw [LinearMap.comp_apply, LinearMap.flip_apply, integrateAgainst_apply,
          A.map_separating B U F h₁ h₂ hAB, hrows row,
          zero_tmul, map_zero, mul_zero, map_zero])
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply,
    RelationCertificate.separating_left_interpret, RelationCertificate.interpret_apply,
    map_sum, map_smul, StrataModule.separating_basis_basis, integrateAgainst_apply] using hz

/-- The exact certificate transfer is also available in the right component. -/
theorem certificate_separating_right_eq_zero {m n : ℕ}
    (A : StrataRealization C g₁ (Option S)) (B : StrataRealization C g₂ (Option T))
    (U : StrataRealization C (g₁ + g₂) (S ⊕ T)) (F : SeparatingPushforward C I)
    (h₁ : StableArity g₁ (Option S)) (h₂ : StableArity g₂ (Option T))
    (hAB : A.SeparatingCompatible B U F h₁ h₂) (w : C.H (g₁ + g₂) (S ⊕ T))
    (x : TautologicalStratum g₁ (Option S))
    (columns : Fin n → TautologicalStratum g₂ (Option T))
    (rows : Fin m → RelationCertificate.Coordinates n)
    (requested : RelationCertificate.Coordinates n)
    (certificate : RelationCertificate.Certificate m)
    (hcheck : RelationCertificate.check rows requested certificate = true)
    (hrows : ∀ row, B.map (RelationCertificate.interpret columns (rows row)) = 0) :
    (∑ i, requested i • I.integrate (g₁ + g₂) (S ⊕ T) (StableArity.separating h₁ h₂)
      (w * U.map (StrataModule.basis (x.separating (columns i))))) = 0 := by
  have hz := RelationCertificate.evaluation_eq_zero columns rows requested certificate hcheck
    ((U.integrateAgainst I (StableArity.separating h₁ h₂) w).comp
      (StrataModule.separating (StrataModule.basis x))) (by
        intro row
        rw [LinearMap.comp_apply, integrateAgainst_apply,
          A.map_separating B U F h₁ h₂ hAB, hrows row,
          tmul_zero, map_zero, mul_zero, map_zero])
  simpa only [LinearMap.comp_apply, RelationCertificate.separating_right_interpret,
    RelationCertificate.interpret_apply, map_sum, map_smul,
    StrataModule.separating_basis_basis, integrateAgainst_apply] using hz

end StrataRealization

end AxiomaticGW
