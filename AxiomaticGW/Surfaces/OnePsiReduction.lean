/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.OnePsiComparison
public import AxiomaticGW.Surfaces.FirstDescendantReduction
public import AxiomaticGW.Coefficients.AffineSubstitution

/-!
# Normalizing primary and first-power surface ancestors

The primitive rational-tail comparison converts a first-power ancestor to
stable-map descendants. String, dilaton and divisor then leave the canonical
point and one-descendant families. Every correction retains its full curve
class. Higher cotangent powers remain explicitly tagged ancestor variables.
-/

@[expose] public section

namespace AxiomaticGW
namespace SurfaceAncestorKey
variable {X : SurfaceTarget}

/-- The selected occurrence, retaining its paired state and power. -/
def onePsiInsertion (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) : SurfaceInsertion X :=
  q.orderedInsertions.get (q.onePsiMark h)

theorem onePsiInsertion_mem (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) :
    q.onePsiInsertion h ∈ q.insertions := q.ordered_get_mem _

theorem onePsiInsertion_power (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) :
    (q.onePsiInsertion h).psi = 1 := by
  change q.orderedPowers (q.onePsiMark h) = 1
  rw [q.orderedPowers_onePsi h, Pi.single_eq_same]

/-- The remainder has no hidden cotangent powers. -/
theorem onePsi_remainder_primary (q : SurfaceAncestorKey X) (h : q.totalPsi = 1)
    (s : SurfaceInsertion X) (hs : s ∈ q.insertions.erase (q.onePsiInsertion h)) :
    s.psi = 0 := by
  have he : q.insertions = q.onePsiInsertion h ::ₘ q.insertions.erase (q.onePsiInsertion h) :=
    (Multiset.cons_erase (q.onePsiInsertion_mem h)).symm
  have ht := h
  rw [totalPsi, he, Multiset.map_cons, Multiset.sum_cons, q.onePsiInsertion_power h] at ht
  have hz : ((q.insertions.erase (q.onePsiInsertion h)).map SurfaceInsertion.psi).sum = 0 := by
    omega
  exact (Multiset.sum_eq_zero_iff.mp hz) s.psi (Multiset.mem_map.mpr ⟨s, hs, rfl⟩)

/-- Erase just the unique descendant occurrence, preserving repeated primary labels. -/
def onePsiPrimaries (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) :
    Multiset (SurfaceBasisLabel X) :=
  (q.insertions.erase (q.onePsiInsertion h)).map SurfaceInsertion.label

variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Sorting is sound independently of the geometric cotangent comparison. -/
theorem descendantEval_eq_query (U : UnstableDescendantConventions M I)
    (q : SurfaceAncestorKey X) : q.descendantEval U = q.descendantQuery.eval U :=
  (congrArg (descendantEval U) q.of_ordered_eq).symm.trans
    (descendantEval_ofLabels U _ _ _ _ _ _)

/-- Separate a specified first-power occurrence from primary occurrences. -/
theorem descendantEval_eq_first_of_cons (U : UnstableDescendantConventions M I)
    (q : SurfaceAncestorKey X) (b : SurfaceBasisLabel X) (m : Multiset (SurfaceInsertion X))
    (hi : q.insertions = ⟨b, 1⟩ ::ₘ m) (hm : ∀ s ∈ m, s.psi = 0) :
    q.descendantEval U = SurfaceFirstDescendant.eval U q.genus q.beta b
      (m.map SurfaceInsertion.label) := by
  rcases q with ⟨g, beta, ins, stable⟩
  dsimp only at hi
  subst ins
  rw [descendantEval, SurfaceFirstDescendant.invariant_relabel U g beta _ _ Multiset.consEquiv,
    SurfaceFirstDescendant.eval_map]
  congr 1
  · funext s
    cases s with
    | none => rfl
    | some s => exact hm _ Multiset.coe_mem
  · funext s; cases s <;> rfl

/-- The selected occurrence yields exactly the numerical family normalized above. -/
theorem descendantQuery_eq_first (U : UnstableDescendantConventions M I)
    (q : SurfaceAncestorKey X) (h : q.totalPsi = 1) :
    q.descendantQuery.eval U = SurfaceFirstDescendant.eval U q.genus q.beta
      (q.onePsiInsertion h).label (q.onePsiPrimaries h) := by
  rw [← q.descendantEval_eq_query U]
  apply descendantEval_eq_first_of_cons U q (q.onePsiInsertion h).label
    (q.insertions.erase (q.onePsiInsertion h))
  · have he : q.onePsiInsertion h = ⟨(q.onePsiInsertion h).label, 1⟩ := by
      cases hi : q.onePsiInsertion h with
      | mk label psi =>
        have hp := q.onePsiInsertion_power h
        rw [hi] at hp
        exact congrArg (fun k ↦ (⟨label, k⟩ : SurfaceInsertion X)) hp
    rw [← he]
    exact (Multiset.cons_erase (q.onePsiInsertion_mem h)).symm
  · exact q.onePsi_remainder_primary h

end SurfaceAncestorKey

namespace SurfacePolynomialReduction

/-- Each comparison correction has a genuinely smaller main curve class,
not merely a renamed class of equal anticanonical energy. -/
theorem normalizedTail_energy_lt (X : SurfaceTarget) (beta : X.Curve)
    (split : X.Curve × X.Curve) (hs : split ∈ X.positiveTailSplittings beta) :
    X.effective.energy split.1 < X.effective.energy beta :=
  RationalTailIntersection.main_energy_lt (D := X.effective) beta
    ⟨split, by rw [← X.positiveTailSplittings_eq]; exact hs⟩

/-- Apply the primary reduction at class zero as well when genus is at least two. -/
def canonicalPrimaryTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    RationalTerms (Variable X) :=
  if 2 ≤ q.genus ∧ q.IsPrimary then
    RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.primaryTerms q.genus q.beta q.primaryLabels)
  else basicTerms q

/-- First-power ancestors are converted with the negative rational-tail
correction, then reduced to the canonical stable-map descendant families. -/
def normalizedTerms {X : SurfaceTarget} (q : SurfaceAncestorKey X) :
    RationalTerms (Variable X) :=
  if h : 2 ≤ q.genus ∧ q.totalPsi = 1 then
    RationalTerms.rename Sum.inr (SurfaceFirstDescendant.terms q.genus q.beta
      (q.onePsiInsertion h.2).label (q.onePsiPrimaries h.2)) +
      ∑ split ∈ X.positiveTailSplittings q.beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale
          (-SurfaceDescendant.firstCalibrationMatrix X split.2 b
            (q.orderedLabels (q.onePsiMark h.2)))
          (canonicalPrimaryTerms (SurfaceAncestorKey.ofLabels q.genus
            (Fin q.orderedInsertions.length) q.ordered_stable split.1 0
            (Function.update q.orderedLabels (q.onePsiMark h.2) b)))
  else canonicalPrimaryTerms q

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

theorem eval_canonicalPrimaryTerms (U : UnstableDescendantConventions M I)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (q : SurfaceAncestorKey X) :
    RationalTerms.eval (variableEval U P) (canonicalPrimaryTerms q) = q.eval Omega P I := by
  unfold canonicalPrimaryTerms
  split_ifs with h
  · rw [RationalTerms.eval_rename]
    change RationalTerms.eval (SurfaceQuery.eval U) _ = _
    rw [SurfaceFirstDescendant.eval_primaryTerms U T laws H hpair q.genus h.1]
    exact (q.eval_eq_primary U P h.2).symm
  · exact eval_basicTerms U P T laws H hpair q

/-- Normalization is a consequence of the primitive cotangent comparison
and existing string/divisor laws, preserving both variable interpretations. -/
theorem eval_normalizedTerms_of_calibration (U : UnstableDescendantConventions M I)
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
    RationalTerms.eval (variableEval U P) (normalizedTerms q) = q.eval Omega P I := by
  unfold normalizedTerms
  split_ifs with h
  · have he := eval_onePsiTerms_of_calibration U P T laws H hpair K hcal q
    rw [onePsiTerms, dif_pos h.2] at he
    simp only [RationalTerms.eval_add, RationalTerms.eval_term,
      Multiset.map_singleton, Multiset.prod_singleton, Algebra.algebraMap_self_apply,
      one_mul, variableEval, RationalTerms.eval_sum, RationalTerms.eval_scale,
      eval_basicTerms U P T laws H hpair] at he
    simp only [RationalTerms.eval_add, RationalTerms.eval_rename, RationalTerms.eval_sum,
      RationalTerms.eval_scale, Algebra.algebraMap_self_apply,
      eval_canonicalPrimaryTerms U P T laws H hpair]
    change RationalTerms.eval (SurfaceQuery.eval U) _ + _ = _
    rw [SurfaceFirstDescendant.eval_terms U T laws H hpair q.genus h.1,
      ← q.descendantQuery_eq_first U h.2]
    exact he
  · exact eval_canonicalPrimaryTerms U P T laws H hpair q

/-- The first calibration coefficient is reconstructed from the existing
finite rational seeds and WDVV geometry, rather than assumed as an oracle. -/
theorem eval_normalizedTerms (U : UnstableDescendantConventions M I)
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
    RationalTerms.eval (variableEval U P) (normalizedTerms q) = q.eval Omega P I :=
  eval_normalizedTerms_of_calibration U P T laws H hpair K
    (SurfaceDescendant.firstCalibrationMatrix_eq Z F N J hsource hboundary p hp P T U laws H
      hpair hline hE houtput) q

end SurfacePolynomialReduction
end AxiomaticGW
