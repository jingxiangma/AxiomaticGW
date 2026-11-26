/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GluingEvaluation
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Surface ancestor polynomials with symmetric component variables

A variable retains genus, the full curve class, and the multiset of paired
state labels and cotangent powers. Equal insertions are counted with their
multiplicities; forgetting their ordering is justified by the existing GW
relabelling law. Polynomial arithmetic collects coincident monomials with
their exact rational coefficients.

These are polynomials in actual ancestor invariants, not their numerical
answers. The interpretation theorem is conditional only on the same metric
identification and geometric inputs as the preceding Getzler evaluation.
-/

@[expose] public section

namespace AxiomaticGW

/-- A stable ancestor variable with permutation-invariant insertion data. -/
structure SurfaceAncestorKey (X : SurfaceTarget) where
  /-- Genus of this connected component. -/
  genus : ℕ
  /-- Every effective curve coordinate is retained. -/
  beta : X.Curve
  /-- Paired state/power data, with repeated insertions counted separately. -/
  insertions : Multiset (SurfaceInsertion X)
  /-- The component is in the stable-curve domain of ancestor integration. -/
  stable : 3 ≤ 2 * genus + insertions.card

namespace SurfaceAncestorKey

/-- Equality depends only on the query data, not on the stability proof. -/
theorem eq_iff {X : SurfaceTarget} (p q : SurfaceAncestorKey X) :
    p = q ↔ p.genus = q.genus ∧ p.beta = q.beta ∧ p.insertions = q.insertions := by
  cases p
  cases q
  simp only [SurfaceAncestorKey.mk.injEq]

/-- Decide data equality without dependent transports through stability proofs.
This also reduces in the kernel for nontrivial multiset permutations. -/
instance {X : SurfaceTarget} : DecidableEq (SurfaceAncestorKey X) := fun p q ↦
  decidable_of_iff (p.genus = q.genus ∧ p.beta = q.beta ∧ p.insertions = q.insertions)
    (eq_iff p q).symm

/-- The occurrence type retains separate markings for repeated insertions. -/
theorem stableArity {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    StableArity q.genus q.insertions := by
  simpa only [StableArity, Multiset.card_coe] using q.stable

/-- Collect labelled insertions without losing their powers or multiplicities. -/
def ofLabels {X : SurfaceTarget} (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    SurfaceAncestorKey X where
  genus := g
  beta := beta
  insertions := (Finset.univ : Finset S).val.map (fun s ↦ ⟨a s, k s⟩)
  stable := by
    simpa only [StableArity, Multiset.card_map, Finset.card_val, Finset.card_univ] using h

/-- Each member of a finite type occurs once in its universal multiset. -/
noncomputable def univOccurrences (S : Type) [Fintype S] [DecidableEq S] :
    S ≃ (Finset.univ : Finset S).val where
  toFun s := ⟨s, ⟨0, by
    rw [Multiset.count_eq_one_of_mem (Finset.univ : Finset S).nodup (Finset.mem_univ s)]
    decide⟩⟩
  invFun t := t.1
  left_inv _ := rfl
  right_inv t := by
    rcases t with ⟨s, i, hi⟩
    rw [Multiset.count_eq_one_of_mem (Finset.univ : Finset S).nodup (Finset.mem_univ s)] at hi
    have hi0 : i = 0 := by omega
    subst i
    rfl

/-- Relabelling the original markings as insertion occurrences. -/
noncomputable def occurrenceEquiv {X : SurfaceTarget} (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    S ≃ (ofLabels g S h beta k a).insertions := by
  classical
  exact (univOccurrences S).trans
    ((Finset.univ : Finset S).val.mapEquiv (fun s ↦ (⟨a s, k s⟩ : SurfaceInsertion X)))

theorem occurrenceEquiv_apply {X : SurfaceTarget} (g : ℕ) (S : Type) [Fintype S]
    (h : StableArity g S) (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X)
    (s : S) :
    ((occurrenceEquiv g S h beta k a s : (ofLabels g S h beta k a).insertions) :
      SurfaceInsertion X) = ⟨a s, k s⟩ := by
  classical
  exact Multiset.mapEquiv_apply (Finset.univ : Finset S).val
    (fun s ↦ (⟨a s, k s⟩ : SurfaceInsertion X)) (univOccurrences S s)

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}

/-- Interpret a symmetric variable using the supplied theory's actual invariant. -/
def eval (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C) (q : SurfaceAncestorKey X) : ℚ :=
  Omega.ancestorInvariant P I q.genus q.insertions q.stableArity q.beta
    (fun s ↦ (s : SurfaceInsertion X).psi)
    (fun s ↦ (s : SurfaceInsertion X).label.value)

/-- Symmetric collection is sound by simultaneous relabelling of states and powers. -/
theorem eval_ofLabels
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (g : ℕ) (S : Type) [Fintype S] (h : StableArity g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    (ofLabels g S h beta k a).eval Omega P I = Omega.surfaceVertexValues P I g S h beta k a := by
  let q := ofLabels g S h beta k a
  let e := occurrenceEquiv g S h beta k a
  have hk : (fun t : q.insertions ↦ k (e.symm t)) =
      (fun t : q.insertions ↦ (t : SurfaceInsertion X).psi) := by
    funext t
    have ht := congrArg SurfaceInsertion.psi (occurrenceEquiv_apply g S h beta k a (e.symm t))
    change ((e (e.symm t) : q.insertions) : SurfaceInsertion X).psi = k (e.symm t) at ht
    simpa only [Equiv.apply_symm_apply] using ht.symm
  have ha : (fun s ↦ ((e s : q.insertions) : SurfaceInsertion X).label.value) =
      (fun s ↦ (a s).value) := by
    funext s
    rw [occurrenceEquiv_apply]
  have hr := congrArg
    (fun f ↦ f (fun t : q.insertions ↦ (t : SurfaceInsertion X).label.value))
    (Omega.ancestorInvariant_relabel P I g S q.insertions h q.stableArity e beta k)
  rw [MultilinearMap.domDomCongr_apply, hk, ha] at hr
  exact hr.symm

/-- Exact component symbol used by the executable graph evaluator. -/
noncomputable def vertexVariables (X : SurfaceTarget) :
    SurfaceVertexValues X (MvPolynomial (SurfaceAncestorKey X) ℚ) :=
  fun g S _ h beta k a ↦ MvPolynomial.X (ofLabels g S h beta k a)

end SurfaceAncestorKey

namespace GluingExpression

/-- Collect equal component monomials in the standard polynomial ring. -/
noncomputable def surfacePolynomial {X : SurfaceTarget} {g : ℕ} {S : Type} [Fintype S]
    (x : GluingExpression g S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) : MvPolynomial (SurfaceAncestorKey X) ℚ :=
  x.surfaceEval X (SurfaceAncestorKey.vertexVariables X) beta k a

/-- Polynomial variables denote actual component ancestors, with no ordering assumption. -/
theorem aeval_surfacePolynomial {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    MvPolynomial.aeval (SurfaceAncestorKey.eval Omega P I) (x.surfacePolynomial beta k a) =
      x.gwAncestorContraction Omega P I beta k (fun s ↦ (a s).value) := by
  rw [surfacePolynomial, surfaceEval_map]
  simp only [SurfaceAncestorKey.vertexVariables, MvPolynomial.aeval_X,
    SurfaceAncestorKey.eval_ofLabels]
  exact x.surfaceEval_eq_gwAncestorContraction Omega P I hp beta k a

end GluingExpression

namespace GetzlerGraphs

/-- The exact original Getzler request as a polynomial in symmetric component variables. -/
noncomputable def surfacePolynomial {X : SurfaceTarget}
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    MvPolynomial (SurfaceAncestorKey X) ℚ :=
  surfaceEquation X (SurfaceAncestorKey.vertexVariables X) n beta k a

/-- Evaluation of the collected polynomial preserves the explicit finite equation. -/
theorem aeval_surfacePolynomial {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (I : StableCurveIntegration C)
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X) :
    MvPolynomial.aeval (SurfaceAncestorKey.eval Omega P I) (surfacePolynomial n beta k a) =
      surfaceEquation X (Omega.surfaceVertexValues P I) n beta k a := by
  simp only [surfacePolynomial, surfaceEquation, surfaceChannel, map_sum, map_mul,
    AlgHom.commutes, map_list_sum, List.map_map, Function.comp_def,
    GluingExpression.surfaceEval_map, SurfaceAncestorKey.vertexVariables,
    MvPolynomial.aeval_X, SurfaceAncestorKey.eval_ofLabels]

/-- The incoming certificate proves the symmetric polynomial equation for the actual theory. -/
theorem exchange_surfacePolynomial_eq_zero {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (I : StableCurveIntegration C)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (H : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (expression i).Compatible A F N)
    (G : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (A 1 (Fin 4)).map (cycle x) = G.cycle x)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C)
    (hp : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)
    (n : ℕ)
    (houtput : ∀ i z, z ∈ (expression i).addMarkings n → z.Compatible A F N)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 4) → ℕ)
    (a : ExtraMarkings n (Fin 4) → SurfaceBasisLabel X)
    (p : RelationCertificate.Presentation 1 (Fin 4) 1 33) (haccept : AcceptsExchange p) :
    MvPolynomial.aeval (SurfaceAncestorKey.eval Omega P I) (surfacePolynomial n beta k a) = 0 := by
  rw [aeval_surfacePolynomial]
  exact exchange_surfaceEquation_eq_zero A I F N H hsource G hcycle Omega P hp n
    houtput beta k a p haccept

end GetzlerGraphs

end AxiomaticGW
