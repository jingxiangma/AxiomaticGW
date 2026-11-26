/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.RationalTerms
public import AxiomaticGW.Surfaces.DegreeZeroPolynomial

/-!
# Executable term expansion of surface graph equations

The expansion follows the existing gluing expression, every full-class split,
and every signed inverse-metric state. Its interpretation is proved equal to
the existing evaluator. Applying the already proved primary reductions at the
terminal components removes zero branches before expanding their products.
-/

@[expose] public section

namespace AxiomaticGW

namespace GluingExpression

/-- Finite term expansion with explicit terminal substitutions. -/
def surfaceTerms {σ : Type*} (X : SurfaceTarget)
    (vertex : SurfaceVertexValues X (RationalTerms σ))
    {g : ℕ} {S : Type} [Fintype S] :
    GluingExpression g S → X.Curve → (S → ℕ) → (S → SurfaceBasisLabel X) →
      RationalTerms σ
  | @fundamental g S _ h, beta, k, a => vertex g S h beta k a
  | @relabel _ _ _ _ _ e x, beta, k, a => x.surfaceTerms X vertex beta (k ∘ e) (a ∘ e)
  | @separating _ _ _ _ _ _ x y, beta, k, a =>
      ∑ split ∈ X.splittings beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale b.inverseWeight
          (RationalTerms.mul
            (x.surfaceTerms X vertex split.1 (PsiClasses.separatingLeftPowers k)
              (Option.elim · b (a ∘ Sum.inl)))
            (y.surfaceTerms X vertex split.2 (PsiClasses.separatingRightPowers k)
              (Option.elim · b.dual (a ∘ Sum.inr))))
  | @nonseparating _ _ _ x, beta, k, a =>
      ∑ b : SurfaceBasisLabel X, RationalTerms.scale b.inverseWeight
        (x.surfaceTerms X vertex beta (PsiClasses.nonseparatingPowers k)
          (Option.elim · b (fun t ↦ Option.elim t b.dual a)))

/-- Term expansion commutes with interpretation, for every terminal assignment. -/
theorem eval_surfaceTerms {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (X : SurfaceTarget) (vertex : SurfaceVertexValues X (RationalTerms σ))
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    RationalTerms.eval v (x.surfaceTerms X vertex beta k a) =
      x.surfaceEval X (fun g S _ h beta k a ↦ RationalTerms.eval v (vertex g S h beta k a))
        beta k a := by
  induction x generalizing beta with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
      simp only [surfaceTerms, surfaceEval, RationalTerms.eval_sum,
        RationalTerms.eval_scale, RationalTerms.eval_mul, ihx, ihy]
  | nonseparating x ih =>
      simp only [surfaceTerms, surfaceEval, RationalTerms.eval_sum,
        RationalTerms.eval_scale, ih]

end GluingExpression

namespace SurfacePolynomialReduction

/-- Both existing primary reduction stages, executed at one terminal component. -/
def primaryTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) : RationalTerms (Variable X) :=
  match reduceVariable q with
  | none => 0
  | some (c, v) =>
      match degreeZeroValue? v with
      | some d => RationalTerms.term (c * d) 0
      | none => RationalTerms.term c {v}

/-- Early execution has exactly the same polynomial as the two proved substitutions. -/
theorem polynomial_primaryTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    RationalTerms.polynomial (primaryTerms q) = reduceDegreeZero X (variablePolynomial q) := by
  unfold primaryTerms variablePolynomial
  cases h : reduceVariable q with
  | none => simp only [RationalTerms.polynomial, RationalTerms.eval_zero, map_zero]
  | some cv =>
      obtain ⟨c, v⟩ := cv
      simp only [reduceDegreeZero, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, degreeZeroPolynomial]
      cases hv : degreeZeroValue? v with
      | none =>
          simp only [RationalTerms.polynomial, RationalTerms.eval_term,
            Multiset.map_singleton, Multiset.prod_singleton]
      | some d =>
          simp only [RationalTerms.polynomial, RationalTerms.eval_term,
            Multiset.map_zero, Multiset.prod_zero, mul_one, map_mul]
          rfl

/-- Terminal component data retain full class, genus and insertion multiplicities. -/
def primaryVertexTerms (X : SurfaceTarget) : SurfaceVertexValues X (RationalTerms (Variable X)) :=
  fun g S _ h beta k a ↦ primaryTerms (SurfaceAncestorKey.ofLabels g S h beta k a)

/-- Genus-zero component reduction needs no elliptic seed values. -/
theorem eval_primaryTerms_of_genus_zero {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (q : SurfaceAncestorKey X) (hg : q.genus = 0) :
    RationalTerms.eval (variableEval U P) (primaryTerms q) = q.eval Omega P I := by
  unfold primaryTerms reduceVariable
  split_ifs with hd hp hc
  · simp only [RationalTerms.eval_zero]
    have h := q.eval_primary_reduced U P T S H hpair hp.1 hp.2
    simpa only [hc, zero_mul] using h.symm
  · simp only [degreeZeroValue?, RationalTerms.eval_term, Multiset.map_singleton,
      Multiset.prod_singleton, Algebra.algebraMap_self_apply, variableEval]
    exact (q.eval_primary_reduced U P T S H hpair hp.1 hp.2).symm
  · simp only [degreeZeroValue?, hg, ite_true]
    split_ifs with hzero
    · simp only [RationalTerms.eval_term, one_mul, Multiset.map_zero,
        Multiset.prod_zero, mul_one, Algebra.algebraMap_self_apply]
      rw [q.eval_eq_primary U P hzero.2, hg, hzero.1]
      exact (SurfacePrimary.eval_genus_zero_zero U T S q.primaryLabels).symm
    · simp only [RationalTerms.eval_term, Multiset.map_singleton,
        Multiset.prod_singleton, Algebra.algebraMap_self_apply, one_mul, variableEval]
  · simp only [RationalTerms.eval_zero]
    exact (q.eval_eq_zero_of_dimension_incompatible P T hd).symm

end SurfacePolynomialReduction

namespace GluingExpression

/-- Every component of a genus-zero gluing expression has genus zero.
Its reduced contraction therefore requires no genus-one seed assumptions. -/
theorem eval_primaryTerms_of_genus_zero {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (S : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    {g : ℕ} {S' : Type} [Fintype S'] (x : GluingExpression g S') (hg : g = 0)
    (beta : X.Curve) (k : S' → ℕ) (a : S' → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
      (x.surfaceTerms X (SurfacePolynomialReduction.primaryVertexTerms X) beta k a) =
      x.gwAncestorContraction Omega P I beta k (fun s ↦ (a s).value) := by
  induction x generalizing beta with
  | fundamental g Marks h =>
    exact (SurfacePolynomialReduction.eval_primaryTerms_of_genus_zero U P T S H hpair
      (SurfaceAncestorKey.ofLabels g Marks h beta k a) hg).trans
        (SurfaceAncestorKey.eval_ofLabels Omega P I g Marks h beta k a)
  | relabel e x ih => exact ih hg beta (k ∘ e) (a ∘ e)
  | separating x y ihx ihy =>
    simp only [surfaceTerms, RationalTerms.eval_sum, RationalTerms.eval_scale,
      RationalTerms.eval_mul, gwAncestorContraction, sum_apply, T.pairing_eq,
      SurfaceCohomology.pairContract_eq_sum, X.splittings_eq, Algebra.algebraMap_self_apply]
    apply Finset.sum_congr rfl
    intro split _
    apply Finset.sum_congr rfl
    intro b _
    rw [ihx (Nat.eq_zero_of_add_eq_zero_right hg), ihy (Nat.eq_zero_of_add_eq_zero_left hg)]
    congr 2 <;> congr 1 <;> funext s <;> cases s <;> rfl
  | nonseparating x ih => omega

end GluingExpression

namespace GetzlerGraphs

/-- Expand the exact held Getzler combination without changing any graph weight. -/
def surfaceTerms {σ : Type*} (X : SurfaceTarget)
    (vertex : SurfaceVertexValues X (RationalTerms σ))
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) : RationalTerms σ :=
  ∑ i, RationalTerms.scale (requested i)
    ((((expression i).addMarkings n).map fun z ↦ z.surfaceTerms X vertex beta k a).sum)

/-- The finite expansion denotes precisely the previous surface equation. -/
theorem eval_surfaceTerms {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (X : SurfaceTarget) (vertex : SurfaceVertexValues X (RationalTerms σ))
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.eval v (surfaceTerms X vertex n beta k a) =
      surfaceEquation X
        (fun g S _ h beta k a ↦ RationalTerms.eval v (vertex g S h beta k a)) n beta k a := by
  simp only [surfaceTerms, surfaceEquation, surfaceChannel, RationalTerms.eval_sum,
    RationalTerms.eval_scale, RationalTerms.eval_list_sum, List.map_map,
    Function.comp_def, GluingExpression.eval_surfaceTerms]

/-- Executable expansion after the sound dimension and primary reductions. -/
def primaryTerms (X : SurfaceTarget)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms (SurfacePolynomialReduction.Variable X) :=
  surfaceTerms X (SurfacePolynomialReduction.primaryVertexTerms X) n beta k a

/-- The executable reduced expansion equals the existing reduced polynomial. -/
theorem polynomial_primaryTerms (X : SurfaceTarget)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    RationalTerms.polynomial (primaryTerms X n beta k a) =
      SurfacePolynomialReduction.reduceDegreeZero X
        (SurfacePolynomialReduction.reduce X (surfacePolynomial n beta k a)) := by
  unfold RationalTerms.polynomial primaryTerms
  rw [eval_surfaceTerms]
  simp only [surfacePolynomial, surfaceEquation, surfaceChannel, map_sum, map_mul,
    AlgHom.commutes, map_list_sum, List.map_map, Function.comp_def,
    GluingExpression.surfaceEval_map, SurfaceAncestorKey.vertexVariables,
    SurfacePolynomialReduction.reduce, MvPolynomial.aeval_X,
    SurfacePolynomialReduction.primaryVertexTerms,
    ← SurfacePolynomialReduction.polynomial_primaryTerms, RationalTerms.polynomial]

/-- An exact finite check against the held graph request transfers the original
Getzler certificate to the proposed terms, evaluated as actual GW invariants. -/
theorem exchange_checkedPrimaryTerms_eq_zero {X : SurfaceTarget}
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
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (result : RationalTerms (SurfacePolynomialReduction.Variable X))
    (hterms : RationalTerms.Equivalent (primaryTerms X n beta k a) result)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (haccept : AcceptsExchange p) :
    RationalTerms.eval (SurfacePolynomialReduction.variableEval U P) result = 0 := by
  rw [← RationalTerms.aeval_polynomial,
    ← RationalTerms.polynomial_eq_of_equivalent _ _ hterms, polynomial_primaryTerms]
  exact exchange_primarySurfacePolynomial_eq_zero A I F N H hsource G hcycle Omega P T U
    S Hdiv hpair hH hE n houtput beta k a p haccept

end GetzlerGraphs

end AxiomaticGW
