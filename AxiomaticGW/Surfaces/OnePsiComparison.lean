/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.MixedAncestorReduction
public import AxiomaticGW.Surfaces.DescendantKeys

/-!
# One-power ancestor comparison for the surface reconstruction equations

A single ancestor cotangent power equals the corresponding stable-map
descendant minus the positive-degree rational-tail contribution. The tail
coefficient is the already reconstructed first calibration matrix. The
remaining components are primary ancestors, and every tail strictly lowers
the full curve energy. The original ancestor/descendant variable tags are
retained, so no comparison is silently presumed.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceAncestorKey
variable {X : SurfaceTarget}

/-- The same insertion data, interpreted as a stable-map descendant request. -/
def descendantQuery (q : SurfaceAncestorKey X) : SurfaceQuery X :=
  ⟨q.genus, q.beta, q.orderedInsertions⟩

/-- A total power of one selects a genuine unique positive marking. -/
def onePsiMark (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) :
    Fin q.orderedInsertions.length :=
  q.positiveMark (fun hp ↦ by
    have hz := q.totalPsi_eq_zero_iff.mpr hp
    omega)

/-- All other occurrences have zero power, including repeated state labels. -/
theorem orderedPowers_onePsi (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) :
    q.orderedPowers = Pi.single (q.onePsiMark h) 1 := by
  have hs : 0 < q.orderedPowers (q.onePsiMark h) := q.positiveMark_pos _
  have ht : ∑ i, q.orderedPowers i = 1 := q.sum_orderedPowers.trans h
  have hle := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (q.orderedPowers i))
    (Finset.mem_univ (q.onePsiMark h))
  have hone : q.orderedPowers (q.onePsiMark h) = 1 := by omega
  funext i
  by_cases hi : i = q.onePsiMark h
  · subst i
    rw [Pi.single_eq_same, hone]
  · rw [Pi.single_eq_of_ne hi]
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin q.orderedInsertions.length))
      q.orderedPowers (Finset.mem_univ (q.onePsiMark h))
    have hz : ∑ j ∈ (Finset.univ : Finset (Fin q.orderedInsertions.length)).erase
        (q.onePsiMark h), q.orderedPowers j = 0 := by omega
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ Nat.zero_le _)).mp hz i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

end SurfaceAncestorKey

namespace SurfacePolynomialReduction

/-- Execute the existing dimension/primary substitution in the rational-term format. -/
def basicTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) : RationalTerms (Variable X) :=
  match reduceVariable q with
  | none => 0
  | some (c, v) => RationalTerms.term c {v}

/-- The primary substitution has exactly its previously proved polynomial. -/
theorem polynomial_basicTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    RationalTerms.polynomial (basicTerms q) = variablePolynomial q := by
  unfold basicTerms variablePolynomial
  cases reduceVariable q with
  | none => rfl
  | some cv =>
    simp only [RationalTerms.polynomial, RationalTerms.eval_term,
      Multiset.map_singleton, Multiset.prod_singleton]
    rfl

/-- Every positive tail is subtracted before primary reduction on the main component. -/
def onePsiTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) : RationalTerms (Variable X) :=
  if h : q.totalPsi = 1 then
    RationalTerms.term 1 {.inr q.descendantQuery} +
      ∑ split ∈ X.positiveTailSplittings q.beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale
          (-SurfaceDescendant.firstCalibrationMatrix X split.2 b
            (q.orderedLabels (q.onePsiMark h)))
          (basicTerms (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
            q.ordered_stable split.1 0 (Function.update q.orderedLabels (q.onePsiMark h) b)))
  else basicTerms q

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- The rational format inherits the original substitution theorem without new assumptions. -/
theorem eval_basicTerms (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (q : SurfaceAncestorKey X) :
    RationalTerms.eval (variableEval U P) (basicTerms q) = q.eval Omega P I := by
  rw [← RationalTerms.aeval_polynomial, polynomial_basicTerms]
  exact aeval_variablePolynomial U P T laws H hpair q

/-- Solving the primitive mixed comparison for its ancestor term gives the minus sign. -/
theorem eval_onePsiTerms_of_calibration (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (K : RationalTailIntersection G St P)
    (hcal : ∀ beta row col, SurfaceDescendant.firstCalibrationMatrix X beta row col =
      row.coordinate (U.calibrationCoefficient 1 beta col.value))
    (q : SurfaceAncestorKey X) :
    RationalTerms.eval (variableEval U P) (onePsiTerms q) = q.eval Omega P I := by
  unfold onePsiTerms
  split_ifs with h
  · let s := q.onePsiMark h
    have hk : Function.update (0 : Fin q.orderedInsertions.length → ℕ) s 1 =
        q.orderedPowers := by
      rw [q.orderedPowers_onePsi h]
      rfl
    have he := K.mixed_step_at q.genus (Fin q.orderedInsertions.length) q.ordered_stable
      s q.beta 0 0 0 (fun t ↦ (q.orderedLabels t).value)
    have hz : Function.update (0 : Fin q.orderedInsertions.length → ℕ) s 0 = 0 :=
      Function.update_eq_self s 0
    simp only [Nat.zero_add, Pi.zero_apply, hk, hz] at he
    rw [M.mixedInvariant_zero_ancestor] at he
    simp only [M.mixedInvariant_zero_descendant] at he
    have ht : (∑ split : ↥(X.effective.positiveTailSplittings q.beta),
        Omega.ancestorInvariant P I q.genus (Fin q.orderedInsertions.length)
          q.ordered_stable split.val.1 0
          (Function.update (fun t ↦ (q.orderedLabels t).value) s
            (U.calibrationCoefficient 1 split.val.2 (q.orderedLabels s).value))) =
        ∑ split ∈ X.positiveTailSplittings q.beta, ∑ b : SurfaceBasisLabel X,
          SurfaceDescendant.firstCalibrationMatrix X split.2 b (q.orderedLabels s) *
            (SurfaceAncestorKey.ofLabels q.genus (Fin q.orderedInsertions.length)
              q.ordered_stable split.1 0 (Function.update q.orderedLabels s b)).eval Omega P I := by
      conv_rhs => rw [X.positiveTailSplittings_eq, ← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro split _
      rw [SurfaceBasisLabel.multilinear_update_eq_sum]
      simp only [hcal, SurfaceAncestorKey.eval_ofLabels, GromovWittenTheory.surfaceVertexValues]
    rw [ht] at he
    simp only [RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
      Multiset.prod_singleton, Algebra.algebraMap_self_apply, one_mul, variableEval,
      RationalTerms.eval_sum, RationalTerms.eval_scale, eval_basicTerms U P T laws H hpair]
    change _ = Omega.surfaceVertexValues P I q.genus _ q.ordered_stable q.beta
      q.orderedPowers q.orderedLabels + _ at he
    rw [← SurfaceAncestorKey.eval_eq_ordered Omega P I q,
      ← U.invariant_of_stable _ _ q.ordered_stable] at he
    change q.descendantQuery.eval U = q.eval Omega P I + _ at he
    simp only [neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    exact sub_eq_iff_eq_add.mpr he
  · exact eval_basicTerms U P T laws H hpair q

/-- The comparison uses only the existing WDVV geometry, finite rational
seeds and primitive virtual cotangent law. The first calibration matrix is
proved from those inputs rather than supplied as a numerical oracle. -/
theorem eval_onePsiTerms (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible Z F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (K : RationalTailIntersection G St P) (q : SurfaceAncestorKey X) :
    RationalTerms.eval (variableEval U P) (onePsiTerms q) = q.eval Omega P I :=
  eval_onePsiTerms_of_calibration U P T laws H hpair K
    (SurfaceDescendant.firstCalibrationMatrix_eq Z F N J hsource hboundary p hp P T U laws H
      hpair hline hE houtput) q

end SurfacePolynomialReduction
end AxiomaticGW
