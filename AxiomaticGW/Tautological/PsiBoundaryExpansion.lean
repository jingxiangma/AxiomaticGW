/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GenusOnePsi
public import AxiomaticGW.Tautological.RationalTail
public import AxiomaticGW.Tautological.GluingAncestors

/-!
# Derived low-genus cotangent boundary recursions

Iterate the existing one-marking psi comparison, using an explicit raw
rational-tail gluing expression and primitive universal-curve base change.
The genus-zero base psi class vanishes by dimension. The genus-one base is
the original claim-bound 3-spin certificate in `GenusOnePsi`.

Each expansion is a finite list of weighted, undecorated one-edge graphs.
The final theorems integrate against actual curve-class-resolved GW classes
and arbitrary remaining ancestor powers, then apply the established gluing
contraction theorem. All full-class splittings are retained. Geometric row
validity and the identification of the primitive tail divisor remain named
class-level inputs, never assumed numerical recurrences.

These are stable-curve ancestor equations. Turning them into stable-map
descendant equations still requires a geometric cotangent comparison with
actual lower-point GW tail factors. No such identification is asserted here.
-/

@[expose] public section

namespace AxiomaticGW

/-- The original label after the ordered marking additions. -/
def ExtraMarkings.oldLabel {S : Type} : (n : ℕ) → S → ExtraMarkings n S
  | 0, s => s
  | n + 1, s => some (ExtraMarkings.oldLabel n s)

/-- Explicit decision data for the iterated optional label type. -/
def ExtraMarkings.decidableEq (S : Type) [DecidableEq S] :
    (n : ℕ) → DecidableEq (ExtraMarkings n S)
  | 0 => inferInstanceAs (DecidableEq S)
  | n + 1 =>
      letI := ExtraMarkings.decidableEq S n
      inferInstanceAs (DecidableEq (Option (ExtraMarkings n S)))

namespace PsiBoundaryExpansion

/-- Explicit graph expansion under successive forgetting. -/
def terms (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) (base : List (ℚ × GluingExpression g S)) :
    (n : ℕ) → List (ℚ × GluingExpression g (ExtraMarkings n S))
  | 0 => base
  | n + 1 =>
      letI := ExtraMarkings.decidableEq S n
      (terms g S h s base n).flatMap (fun t ↦ t.2.addMarking.map (fun z ↦ (t.1, z))) ++
        [(1, tailExpression g (ExtraMarkings n S) (h.extraMarkings n)
          (ExtraMarkings.oldLabel n s))]

/-- Pullbacks and newly added tails keep every summand in codimension one. -/
theorem terms_edgeCount (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) (base : List (ℚ × GluingExpression g S))
    (hbase : ∀ t ∈ base, t.2.graph.graph.edgeCount = 1) (n : ℕ) :
    ∀ t ∈ terms g S h s base n, t.2.graph.graph.edgeCount = 1 := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
      letI := ExtraMarkings.decidableEq S n
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨y, hy, ht⟩ := List.mem_flatMap.mp ht
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ht
        exact (y.2.addMarking_edgeCount z hz).trans (ih y hy)
      · obtain rfl := List.mem_singleton.mp ht
        exact tailExpression_edgeCount _ _ _ _

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Exact rational combination of the raw gluing classes. -/
noncomputable def value (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    {g : ℕ} {S : Type} [Fintype S] (l : List (ℚ × GluingExpression g S)) : C.H g S :=
  (l.map fun t ↦ t.1 • t.2.classValue F N).sum

/-- Primitive base change pulls back a weighted list with all multiplicities. -/
theorem value_addMarking (F : SeparatingPushforward C I)
    (N : NonseparatingPushforward C I) (H : GluingForgetfulCompatibility F N)
    {g : ℕ} {S : Type} [Fintype S] (h : StableArity g S)
    (l : List (ℚ × GluingExpression g S)) :
    value F N (l.flatMap fun t ↦ t.2.addMarking.map (fun z ↦ (t.1,z))) =
      C.forget g S h (value F N l) := by
  let L := (C.forget g S h).toLinearMap.restrictScalars ℚ
  induction l with
  | nil => simp only [value, List.flatMap_nil, List.map_nil, List.sum_nil, map_zero]
  | cons t ts ih =>
      rw [List.flatMap_cons]
      simp only [value, List.map_append, List.sum_append, List.map_map, Function.comp_def,
        List.map_cons, List.sum_cons] at ih ⊢
      have he : (t.2.addMarking.map (fun x ↦ t.1 • x.classValue F N)).sum =
          t.1 • (t.2.addMarking.map (GluingExpression.classValue F N)).sum := by
        rw [List.smul_sum, List.map_map]
        rfl
      rw [he, t.2.sum_classValue_addMarking F N H, ih]
      change t.1 • L (t.2.classValue F N) + L _ = L (t.1 • t.2.classValue F N + _)
      rw [map_add, map_smul]

/-- Iteration derives the complete boundary expansion from a proved base class identity. -/
theorem psi_eq_value (P : PsiClasses C) (K : PsiForgetFormula P)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hK : TailCompatible K F N)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) (base : List (ℚ × GluingExpression g S))
    (hbase : P.psi g S h s = value F N base) (n : ℕ) :
    P.psi g (ExtraMarkings n S) (h.extraMarkings n) (ExtraMarkings.oldLabel n s) =
      value F N (terms g S h s base n) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
      letI := ExtraMarkings.decidableEq S n
      rw [ExtraMarkings.oldLabel,
        K.psi_eq_forget_add_boundary g (ExtraMarkings n S) (h.extraMarkings n)
          (ExtraMarkings.oldLabel n s), ih,
        hK g (ExtraMarkings n S) (h.extraMarkings n)]
      rw [terms]
      simp only [value, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, one_smul, add_zero]
      congr 1
      exact (value_addMarking F N H (h.extraMarkings n) _).symm

/-- The stable genus-zero three-point psi class vanishes by dimension. -/
theorem psi_zero_three (P : PsiClasses C) (h : StableArity 0 (Fin 3)) (s : Fin 3) :
    P.psi 0 (Fin 3) h s = 0 := by
  apply C.eq_zero_of_dimension_lt 0 (Fin 3) h 1 _ (P.psi_degree _ _ _ _)
  rw [StableArity.dimension_zero_fin_three]
  decide +kernel

/-- The genus-zero boundary expansion needs no independent base relation. -/
def genusZeroTerms (s : Fin 3) (n : ℕ) :
    List (ℚ × GluingExpression 0 (ExtraMarkings n (Fin 3))) :=
  terms 0 (Fin 3) StableArity.zero_fin_three s [] n

/-- The genus-one expansion starts with the raw loop coefficient 1/24. -/
def genusOneTerms (n : ℕ) : List (ℚ × GluingExpression 1 (ExtraMarkings n (Fin 1))) :=
  terms 1 (Fin 1) GenusOnePsi.stableArity 0 [(1 / 24, GenusOnePsi.loopExpression)] n

/-- Every added marking follows from the primitive one-marking psi formula. -/
theorem genusZero_psi_eq_value (P : PsiClasses C) (K : PsiForgetFormula P)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hK : TailCompatible K F N)
    (s : Fin 3) (n : ℕ) :
    P.psi 0 (ExtraMarkings n (Fin 3)) (StableArity.zero_fin_three.extraMarkings n)
        (ExtraMarkings.oldLabel n s) = value F N (genusZeroTerms s n) := by
  apply psi_eq_value P K F N H hK
  rw [psi_zero_three]
  rfl

/-- The original accepted row certificate supplies the only genus-one base relation. -/
theorem genusOne_psi_eq_value (P : PsiClasses C) (K : PsiForgetFormula P)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N) (hK : TailCompatible K F N)
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (p : RelationCertificate.Presentation 1 (Fin 1) 2 3)
    (hp : GenusOnePsi.AcceptsExchange p)
    (hpsi : (A 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (A 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (A 1 (Fin 1)).map
      (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible A F N) (n : ℕ) :
    P.psi 1 (ExtraMarkings n (Fin 1)) (GenusOnePsi.stableArity.extraMarkings n)
        (ExtraMarkings.oldLabel n (0 : Fin 1)) = value F N (genusOneTerms n) := by
  apply psi_eq_value P K F N H hK
  have he := GenusOnePsi.realized_psi p hp (A 1 (Fin 1)) P hpsi hfund hrows
  rw [GenusOnePsi.loopExpression.map_stratum_eq_classValue A F N hloop] at he
  simpa only [value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using he

variable {V B : Type u} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCancelCommMonoid B]
  {D : EffectiveCurveMonoid B}

/-- Integrating a derived psi expansion lowers its exponent and contracts every raw graph.
The supplied class identity is discharged by the low-genus theorems above. -/
theorem ancestor_eq_contractions
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C)
    (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) (l : List (ℚ × GluingExpression g S))
    (hpsi : P.psi g S h s = value F N l)
    (hl : ∀ t ∈ l, t.2.Compatible A F N)
    (beta : B) (k : S → ℕ) (a : S → V) :
    Omega.ancestorInvariant P I g S h beta (k + Pi.single s 1) a =
      (l.map fun t ↦ (algebraMap ℚ R t.1) *
        t.2.gwAncestorContraction Omega P I beta k a).sum := by
  change I.integrate g S h (Omega.omega g S h beta a *
    P.monomial g S h (k + Pi.single s 1)) = _
  rw [P.monomial_add, P.monomial_single, pow_one, hpsi]
  let L : C.H g S →ₗ[ℚ] R := ((I.integrate g S h).comp
    (LinearMap.mulLeft R (Omega.omega g S h beta a * P.monomial g S h k))).restrictScalars ℚ
  rw [← mul_assoc]
  change L (value F N l) = _
  rw [value, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  rw [map_smul]
  have hm := t.2.map_stratum_eq_classValue A F N (hl t ht)
  have hc := congrArg (fun f ↦ f a)
    (t.2.gwAncestorIntegral_eq_contraction A F N Omega P (hl t ht) beta k)
  rw [GluingExpression.gwAncestorIntegral_apply,
    StrataRealization.integrateAgainst_apply, hm] at hc
  change t.1 • I.integrate g S h
    ((Omega.omega g S h beta a * P.monomial g S h k) * t.2.classValue F N) = _
  rw [mul_comm (Omega.omega _ _ _ _ _), hc, Algebra.smul_def]

/-- The genus-zero ancestor recursion is derived from dimension and primitive boundary laws. -/
theorem genusZero_ancestor_eq_contractions
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N) (s : Fin 3) (n : ℕ)
    (hl : ∀ t ∈ genusZeroTerms s n, t.2.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → V) :
    letI := ExtraMarkings.decidableEq (Fin 3) n
    Omega.ancestorInvariant P I 0 (ExtraMarkings n (Fin 3))
        (StableArity.zero_fin_three.extraMarkings n) beta
        (k + Pi.single (ExtraMarkings.oldLabel n s) 1) a =
      ((genusZeroTerms s n).map fun t ↦ (algebraMap ℚ R t.1) *
        t.2.gwAncestorContraction Omega P I beta k a).sum := by
  letI := ExtraMarkings.decidableEq (Fin 3) n
  exact ancestor_eq_contractions A F N Omega P _ _ _ _ _
    (genusZero_psi_eq_value P K F N H hK s n) hl beta k a

/-- The genus-one ancestor recursion consumes the original accepted finite certificate. -/
theorem genusOne_ancestor_eq_contractions
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (Omega : GromovWittenTheory R V B D C) (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : TailCompatible K F N)
    (p : RelationCertificate.Presentation 1 (Fin 1) 2 3)
    (hp : GenusOnePsi.AcceptsExchange p)
    (hpsi : (A 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (A 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (A 1 (Fin 1)).map
      (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible A F N) (n : ℕ)
    (hl : ∀ t ∈ genusOneTerms n, t.2.Compatible A F N)
    (beta : B) (k : ExtraMarkings n (Fin 1) → ℕ) (a : ExtraMarkings n (Fin 1) → V) :
    letI := ExtraMarkings.decidableEq (Fin 1) n
    Omega.ancestorInvariant P I 1 (ExtraMarkings n (Fin 1))
        (GenusOnePsi.stableArity.extraMarkings n) beta
        (k + Pi.single (ExtraMarkings.oldLabel n (0 : Fin 1)) 1) a =
      ((genusOneTerms n).map fun t ↦ (algebraMap ℚ R t.1) *
        t.2.gwAncestorContraction Omega P I beta k a).sum := by
  letI := ExtraMarkings.decidableEq (Fin 1) n
  exact ancestor_eq_contractions A F N Omega P _ _ _ _ _
    (genusOne_psi_eq_value P K F N H hK A p hp hpsi hfund hrows hloop n) hl beta k a

end PsiBoundaryExpansion
end AxiomaticGW
