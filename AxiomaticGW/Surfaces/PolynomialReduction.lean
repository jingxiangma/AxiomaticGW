/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.AncestorPolynomial
public import AxiomaticGW.Surfaces.PrimaryReduction

/-!
# Sound reduction of surface ancestor polynomials

Dimension vanishing applies to every ancestor variable. At nonzero curve
class, primary variables reduce by string and divisor equations to numerical
point queries. These queries may have unstable curve arity. Other variables
remain ancestors: no comparison of nonzero ancestor and descendant powers is
presumed. Every substitution is proved to preserve actual invariant values.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceAncestorKey

/-- Total complex codimension, with multiplicities and powers retained. -/
def totalCodimension {X : SurfaceTarget} (q : SurfaceAncestorKey X) : ℕ :=
  (q.insertions.map (fun s ↦ s.label.codimension + s.psi)).sum

/-- The signed surface virtual-dimension condition. -/
def DimensionCompatible {X : SurfaceTarget} (q : SurfaceAncestorKey X) : Prop :=
  (q.totalCodimension : ℤ) =
    X.c1Degree q.beta + (q.genus : ℤ) - 1 + (q.insertions.card : ℤ)

instance {X : SurfaceTarget} (q : SurfaceAncestorKey X) : Decidable q.DimensionCompatible :=
  inferInstanceAs (Decidable ((_ : ℤ) = _))

/-- Primary insertions have zero cotangent power at every occurrence. -/
def IsPrimary {X : SurfaceTarget} (q : SurfaceAncestorKey X) : Prop :=
  ∀ s ∈ q.insertions, s.psi = 0

instance {X : SurfaceTarget} (q : SurfaceAncestorKey X) : Decidable q.IsPrimary := by
  unfold IsPrimary
  infer_instance

/-- Forget powers only after separately checking that the query is primary. -/
def primaryLabels {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    Multiset (SurfaceBasisLabel X) := q.insertions.map SurfaceInsertion.label

/-- Product of signed divisor intersections; a primary unit gives zero. -/
def primaryCoefficient {X : SurfaceTarget} (q : SurfaceAncestorKey X) : ℚ :=
  (q.primaryLabels.map (SurfaceBasisLabel.primaryFactor q.beta)).prod

/-- The residual point query retains genus and the entire effective class. -/
def pointQuery {X : SurfaceTarget} (q : SurfaceAncestorKey X) : SurfaceQuery X :=
  SurfaceQuery.points X q.genus q.beta (q.primaryLabels.count .point)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- The executable dimension check implies vanishing of the actual ancestor. -/
theorem eval_eq_zero_of_dimension_incompatible
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (q : SurfaceAncestorKey X) (h : ¬q.DimensionCompatible) : q.eval Omega P I = 0 := by
  apply Omega.ancestorInvariant_eq_zero_of_virtual_dimension_ne P I
    q.genus q.insertions q.stableArity q.beta
    (fun s ↦ (s : SurfaceInsertion X).psi)
    (fun s ↦ (s : SurfaceInsertion X).label.codimension)
    (fun s ↦ (s : SurfaceInsertion X).label.value)
  · intro s
    rw [T.degree_eq]
    exact (s : SurfaceInsertion X).label.value_mem_degree
  · intro heq
    apply h
    unfold DimensionCompatible totalCodimension
    rw [← Multiset.map_univ, Multiset.sum_map_add, Nat.cast_add]
    change ((∑ s : q.insertions, (s : SurfaceInsertion X).label.codimension : ℕ) : ℤ) +
      ((∑ s : q.insertions, (s : SurfaceInsertion X).psi : ℕ) : ℤ) = _
    rw [T.dimension_eq, T.c1Degree_eq, Multiset.card_coe] at heq
    rw [heq]
    unfold GWVirtualDimension
    ring

/-- Zero powers identify stable ancestors with the existing full primary
invariant, without a descendant--ancestor comparison at nonzero powers. -/
theorem eval_eq_primary (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (q : SurfaceAncestorKey X) (hq : q.IsPrimary) :
    q.eval Omega P I = SurfacePrimary.eval U q.genus q.beta q.primaryLabels := by
  have hk : (fun s : q.insertions ↦ (s : SurfaceInsertion X).psi) = (fun _ ↦ 0) := by
    funext s
    exact hq _ Multiset.coe_mem
  rw [primaryLabels, SurfacePrimary.eval_map, U.invariant_of_stable _ _ q.stableArity,
    StableMapDescendants.invariant_zero]
  simp only [eval, hk, GromovWittenTheory.ancestorInvariant_apply, PsiClasses.monomial_zero,
    mul_one, LinearMap.compMultilinearMap_apply]

/-- Complete positive-class primary substitution for an ancestor variable. -/
theorem eval_primary_reduced (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (q : SurfaceAncestorKey X) (hq : q.IsPrimary) (hbeta : q.beta ≠ 0) :
    q.eval Omega P I = q.primaryCoefficient * q.pointQuery.eval U := by
  rw [eval_eq_primary U P q hq,
    SurfacePrimary.eval_reduced U T S H hpair q.genus q.beta hbeta,
    pointQuery, SurfaceQuery.eval_points]
  rfl

end SurfaceAncestorKey

namespace SurfacePolynomialReduction

/-- Unreduced ancestors and actual numerical descendant queries remain
distinct. Primary divisor removal may produce an unstable point query. -/
abbrev Variable (X : SurfaceTarget) := SurfaceAncestorKey X ⊕ SurfaceQuery X

/-- Decide the two query tags without transporting through equality of their
payloads. Extensional curve equality must remain reducible during kernel replay. -/
instance {X : SurfaceTarget} : DecidableEq (Variable X)
  | .inl p, .inl q =>
      decidable_of_iff (p = q) ⟨fun h ↦ congrArg Sum.inl h, fun h ↦ Sum.inl.inj h⟩
  | .inr p, .inr q =>
      decidable_of_iff (p = q) ⟨fun h ↦ congrArg Sum.inr h, fun h ↦ Sum.inr.inj h⟩
  | .inl _, .inr _ => isFalse (by intro h; cases h)
  | .inr _, .inl _ => isFalse (by intro h; cases h)

/-- Executable reduction data. `none` is a proved zero; a surviving term is
an exact rational coefficient and its residual variable. -/
def reduceVariable {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    Option (ℚ × Variable X) :=
  if q.DimensionCompatible then
    if q.IsPrimary ∧ q.beta ≠ 0 then
      if q.primaryCoefficient = 0 then none
      else some (q.primaryCoefficient, .inr q.pointQuery)
    else some (1, .inl q)
  else none

/-- Interpret reduction data in the ordinary exact polynomial ring. -/
noncomputable def variablePolynomial {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    MvPolynomial (Variable X) ℚ :=
  match reduceVariable q with
  | none => 0
  | some (c, v) => MvPolynomial.C c * MvPolynomial.X v

/-- Simultaneous substitution collects equal residual monomials. -/
noncomputable def reduce (X : SurfaceTarget) :
    MvPolynomial (SurfaceAncestorKey X) ℚ →ₐ[ℚ] MvPolynomial (Variable X) ℚ :=
  MvPolynomial.aeval variablePolynomial

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Both kinds of residual variable use their existing invariant semantics. -/
noncomputable def variableEval (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) : Variable X → ℚ
  | .inl q => q.eval Omega P I
  | .inr q => q.eval U

/-- Every one-variable reduction preserves the supplied theory's value. -/
theorem aeval_variablePolynomial (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (q : SurfaceAncestorKey X) :
    MvPolynomial.aeval (variableEval U P) (variablePolynomial q) = q.eval Omega P I := by
  unfold variablePolynomial reduceVariable
  split_ifs with hd hp hc
  · simp only [map_zero]
    have h := q.eval_primary_reduced U P T S H hpair hp.1 hp.2
    simpa only [hc, zero_mul] using h.symm
  · simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, variableEval]
    exact (q.eval_primary_reduced U P T S H hpair hp.1 hp.2).symm
  · simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, one_mul, variableEval]
  · simp only [map_zero]
    exact (q.eval_eq_zero_of_dimension_incompatible P T hd).symm

/-- Substitution is sound for any ancestor polynomial, not just a fixed
coefficient probe or marking bound. -/
theorem aeval_reduce (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (p : MvPolynomial (SurfaceAncestorKey X) ℚ) :
    MvPolynomial.aeval (variableEval U P) (reduce X p) =
      MvPolynomial.aeval (SurfaceAncestorKey.eval Omega P I) p := by
  rw [reduce, MvPolynomial.comp_aeval_apply]
  simp only [aeval_variablePolynomial U P T S H hpair]

end SurfacePolynomialReduction

namespace GetzlerGraphs

/-- The original checked Getzler request remains a valid equation after
dimension vanishing and positive-class primary string/divisor reduction. -/
theorem exchange_reducedSurfacePolynomial_eq_zero {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
    (S : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible Adiv)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (haccept : AcceptsExchange p) :
    MvPolynomial.aeval (SurfacePolynomialReduction.variableEval U P)
      (SurfacePolynomialReduction.reduce X (surfacePolynomial n beta k a)) = 0 := by
  rw [SurfacePolynomialReduction.aeval_reduce U P T S Hdiv hpair]
  exact exchange_surfacePolynomial_eq_zero A I F N H hsource G hcycle Omega P
    T.pairing_eq n houtput beta k a p haccept

end GetzlerGraphs

end AxiomaticGW
