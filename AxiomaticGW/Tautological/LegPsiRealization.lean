/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.LegPsi
public import AxiomaticGW.Tautological.StrataRealization
public import AxiomaticGW.Tautological.RelationCertificate
public import AxiomaticGW.CohFT.Ancestors

/-!
# Realization and numerical evaluation of external psi operations

A primitive compatibility law identifies one external psi factor on a graph
with multiplication by that stable-curve cotangent class. The theorems below
derive arbitrary monomials and their linear combinations from that law and
transfer checked relation combinations to integrated cohomology equations.
The supplied realization and its relation vanishing are explicit inputs.
General graph splitting and stable-map descendant comparison are not assumed
to follow from this external psi calculation.
-/

@[expose] public section

namespace AxiomaticGW

open scoped BigOperators

universe u

namespace PsiClasses

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} (P : PsiClasses C)
  {g : ℕ} {S : Type} [Fintype S]

/-- Cotangent monomials multiply by adding their labelled powers. -/
theorem monomial_add (h : StableArity g S) (k l : S → ℕ) :
    P.monomial g S h (k + l) = P.monomial g S h k * P.monomial g S h l := by
  simp only [monomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- A monomial supported at one label is that label's cotangent power. -/
theorem monomial_single (h : StableArity g S) (s : S) (m : ℕ) [DecidableEq S] :
    P.monomial g S h (Pi.single s m) = P.psi g S h s ^ m := by
  unfold monomial
  rw [Finset.prod_eq_single s]
  · rw [Pi.single_eq_same]
  · intro t _ ht
    rw [Pi.single_eq_of_ne ht, pow_zero]
  · intro hs
    exact (hs (Finset.mem_univ s)).elim

end PsiClasses

namespace RelationCertificate

variable {g n : ℕ} {S : Type} [Fintype S]

/-- The graph operation commutes with interpretation of exact coordinates,
so a searched row combination can be multiplied without changing its weights. -/
theorem mulLegPsi_interpret (k : S → ℕ) (columns : Fin n → TautologicalStratum g S)
    (x : Coordinates n) :
    StrataModule.mulLegPsi k (interpret columns x) =
      interpret (fun i ↦ (columns i).addLegPsi k) x := by
  simp only [interpret_apply, map_sum, map_smul, StrataModule.mulLegPsi_basis]

/-- A checked row witness remains a valid formal relation consequence after
the verified external psi operation. Geometric vanishing still needs a
compatible realization and vanishing of the original relation rows. -/
theorem mulLegPsi_check_sound {m : ℕ} (k : S → ℕ)
    (columns : Fin n → TautologicalStratum g S) (rows : Fin m → Coordinates n)
    (requested : Coordinates n) (certificate : Certificate m)
    (h : check rows requested certificate = true) :
    StrataModule.mulLegPsi k (interpret columns requested) ∈
      relationSpan (fun i ↦ (columns i).addLegPsi k) rows := by
  rw [mulLegPsi_interpret]
  exact check_sound _ rows requested certificate h

end RelationCertificate

namespace StrataRealization

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {g : ℕ} {S : Type} [Fintype S]

attribute [local instance] strataRealizationModule

/-- Primitive external cotangent compatibility. In geometry this is the
projection formula and pullback of a marking's cotangent line to its graph
factor. Only one factor is required; higher monomials are derived below. -/
def LegPsiCompatible (A : StrataRealization C g S) (P : PsiClasses C)
    (h : StableArity g S) : Prop :=
  ∀ (x : TautologicalStratum g S) (s : S) (delta : S → ℕ),
    delta s = 1 → (∀ t, t ≠ s → delta t = 0) →
    A.map (StrataModule.basis (x.addLegPsi delta)) =
      A.map (StrataModule.basis x) * P.psi g S h s

/-- The primitive law applies to the usual single-label exponent function.
Its semantic definition does not depend on a choice of decidable equality. -/
theorem map_addLegPsi_one (A : StrataRealization C g S) (P : PsiClasses C)
    (h : StableArity g S) (hA : A.LegPsiCompatible P h)
    (x : TautologicalStratum g S) (s : S) [DecidableEq S] :
    A.map (StrataModule.basis (x.addLegPsi (Pi.single s 1))) =
      A.map (StrataModule.basis x) * P.psi g S h s :=
  hA x s _ (Pi.single_eq_same s 1) (fun _ ht ↦ Pi.single_eq_of_ne ht 1)

/-- Single-label powers follow by natural induction from the primitive law. -/
theorem map_addLegPsi_single (A : StrataRealization C g S) (P : PsiClasses C)
    (h : StableArity g S) (hA : A.LegPsiCompatible P h)
    (x : TautologicalStratum g S) (s : S) (m : ℕ) [DecidableEq S] :
    A.map (StrataModule.basis (x.addLegPsi (Pi.single s m))) =
      A.map (StrataModule.basis x) * P.psi g S h s ^ m := by
  induction m with
  | zero =>
    rw [Pi.single_zero, TautologicalStratum.addLegPsi_zero, pow_zero, mul_one]
  | succ m ih =>
    rw [Pi.single_add, TautologicalStratum.addLegPsi_add,
      A.map_addLegPsi_one P h hA, ih, pow_succ, mul_assoc]

/-- Every external monomial is realized correctly, without an additional
assumption for higher powers or several markings. -/
theorem map_addLegPsi (A : StrataRealization C g S) (P : PsiClasses C)
    (h : StableArity g S) (hA : A.LegPsiCompatible P h)
    (x : TautologicalStratum g S) (k : S → ℕ) :
    A.map (StrataModule.basis (x.addLegPsi k)) =
      A.map (StrataModule.basis x) * P.monomial g S h k := by
  classical
  have hf : ∀ (f : S →₀ ℕ) (x : TautologicalStratum g S),
      A.map (StrataModule.basis (x.addLegPsi f)) =
        A.map (StrataModule.basis x) * P.monomial g S h f := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero =>
      intro x
      rw [Finsupp.coe_zero, TautologicalStratum.addLegPsi_zero]
      simp only [PsiClasses.monomial, Pi.zero_apply, pow_zero,
        Finset.prod_const_one, mul_one]
    | add f l hf hl =>
      intro x
      rw [Finsupp.coe_add, TautologicalStratum.addLegPsi_add,
        hl, hf, P.monomial_add, mul_assoc]
    | single s m =>
      intro x
      rw [Finsupp.single_eq_pi_single, P.monomial_single]
      exact A.map_addLegPsi_single P h hA x s m
  exact hf (Finsupp.equivFunOnFinite.symm k) x

/-- Realization intertwines the actual rational graph operation and
cohomology multiplication on every finite stratum combination. -/
theorem map_mulLegPsi (A : StrataRealization C g S) (P : PsiClasses C)
    (h : StableArity g S) (hA : A.LegPsiCompatible P h)
    (k : S → ℕ) (r : StrataModule g S) :
    A.map (StrataModule.mulLegPsi k r) = A.map r * P.monomial g S h k := by
  have heq : A.map.comp (StrataModule.mulLegPsi k) =
      ((CohFT.multiplyPsi P g S h k).restrictScalars ℚ).comp A.map := by
    apply Finsupp.lhom_ext
    intro x q
    have hsingle : Finsupp.single x q = q • StrataModule.basis x := by
      simp only [StrataModule.basis, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle]
    simp only [LinearMap.comp_apply, map_smul, StrataModule.mulLegPsi_basis]
    exact congrArg (fun z : C.H g S ↦ q • z) (A.map_addLegPsi P h hA x k)
  exact congrArg (fun f ↦ f r) heq

/-- Evaluation against a specified cohomology insertion. The integration
and coefficient restriction come from the existing stable-curve interface. -/
noncomputable def integrateAgainst (A : StrataRealization C g S)
    (I : StableCurveIntegration C) (h : StableArity g S) (w : C.H g S) :
    StrataModule g S →ₗ[ℚ] R :=
  (((I.integrate g S h).comp (LinearMap.mulLeft R w)).restrictScalars ℚ).comp A.map

/-- The evaluator integrates the actual realization times the held insertion. -/
theorem integrateAgainst_apply (A : StrataRealization C g S)
    (I : StableCurveIntegration C) (h : StableArity g S)
    (w : C.H g S) (r : StrataModule g S) :
    A.integrateAgainst I h w r = I.integrate g S h (w * A.map r) := rfl

/-- External graph multiplication inserts the corresponding stable-curve
monomial in the complete integrand. -/
theorem integrateAgainst_mulLegPsi (A : StrataRealization C g S) (P : PsiClasses C)
    (I : StableCurveIntegration C) (h : StableArity g S) (hA : A.LegPsiCompatible P h)
    (w : C.H g S) (k : S → ℕ) (r : StrataModule g S) :
    A.integrateAgainst I h w (StrataModule.mulLegPsi k r) =
      A.integrateAgainst I h (w * P.monomial g S h k) r := by
  rw [integrateAgainst_apply, integrateAgainst_apply, A.map_mulLegPsi P h hA]
  congr 1
  rw [← mul_assoc]
  exact mul_right_comm _ _ _

/-- Checked row combinations yield integrated equations after external psi
multiplication. Only original row vanishing and the primitive compatibility
law are supplied; the multiplied numerical equation is a conclusion. -/
theorem certificate_mulLegPsi_eq_zero {m n : ℕ} (A : StrataRealization C g S)
    (P : PsiClasses C) (I : StableCurveIntegration C) (h : StableArity g S)
    (hA : A.LegPsiCompatible P h) (w : C.H g S) (k : S → ℕ)
    (columns : Fin n → TautologicalStratum g S)
    (rows : Fin m → RelationCertificate.Coordinates n)
    (requested : RelationCertificate.Coordinates n)
    (certificate : RelationCertificate.Certificate m)
    (hcheck : RelationCertificate.check rows requested certificate = true)
    (hrows : ∀ row, A.map (RelationCertificate.interpret columns (rows row)) = 0) :
    (∑ i, requested i • I.integrate g S h
      (w * A.map (StrataModule.basis ((columns i).addLegPsi k)))) = 0 := by
  have hz := RelationCertificate.evaluation_eq_zero columns rows requested certificate hcheck
    (A.integrateAgainst I h (w * P.monomial g S h k)) (by
      intro row
      rw [integrateAgainst_apply, hrows row, mul_zero, map_zero])
  rw [← A.integrateAgainst_mulLegPsi P I h hA w k,
    RelationCertificate.mulLegPsi_interpret] at hz
  simpa only [RelationCertificate.interpret_apply, map_sum, map_smul,
    integrateAgainst_apply] using hz

/-- On the normalized fundamental stratum the evaluator is the existing
class-valued CohFT ancestor, rather than a separately supplied number. -/
theorem integrateAgainst_fundamental {V : Type u} [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V] (A : StrataRealization C g S)
    (P : PsiClasses C) (I : StableCurveIntegration C) (h : StableArity g S)
    (hA : A.LegPsiCompatible P h)
    (hfund : A.map (StrataModule.basis (TautologicalStratum.fundamental g S h)) = 1)
    (Omega : CohFT R V C) (a : S → V) (k : S → ℕ) :
    A.integrateAgainst I h (Omega.omega g S h a)
      (StrataModule.mulLegPsi k
        (StrataModule.basis (TautologicalStratum.fundamental g S h))) =
      Omega.ancestor P I g S h k a := by
  rw [integrateAgainst_apply, A.map_mulLegPsi P h hA, hfund, one_mul,
    CohFT.ancestor_apply]

end StrataRealization

end AxiomaticGW
