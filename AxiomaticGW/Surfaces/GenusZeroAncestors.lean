/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.AncestorMarkings
public import AxiomaticGW.Surfaces.GluingDegree
public import AxiomaticGW.Surfaces.GenusZeroReconstruction

/-!
# Genus-zero ancestor reconstruction at arbitrary marking count

A positive cotangent power selects a retained marking in a computable frame.
The existing geometric psi expansion expresses it as one-edge contractions.
Each component has strictly smaller total cotangent degree. Structural
recursion with that degree as fuel therefore terminates at the already
reconstructed primary sector. Full effective curve splits and the signed
inverse metric are inherited unchanged from the existing gluing evaluator.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero
variable {X : SurfaceTarget}

/-- The number of markings added to the stable rational base. -/
def extraCount (q : SurfaceAncestorKey X) : ℕ := q.orderedInsertions.length - 3

theorem three_le_length (q : SurfaceAncestorKey X) (hg : q.genus = 0) :
    3 ≤ q.orderedInsertions.length := by
  have h := q.stable
  rw [hg, Nat.mul_zero, Nat.zero_add, ← q.orderedInsertions_length] at h
  exact h

/-- Base marking zero is sent to a genuine positive-power occurrence. -/
def ancestorFrame (q : SurfaceAncestorKey X) (hg : q.genus = 0) (hp : ¬q.IsPrimary) :
    ExtraMarkings (extraCount q) (Fin 3) ≃ Fin q.orderedInsertions.length :=
  ExtraMarkings.markingFrame 3 _ (three_le_length q hg) 0 (q.positiveMark hp)

theorem ancestorFrame_old (q : SurfaceAncestorKey X) (hg : q.genus = 0)
    (hp : ¬q.IsPrimary) :
    ancestorFrame q hg hp (ExtraMarkings.oldLabel (extraCount q) (0 : Fin 3)) =
      q.positiveMark hp := ExtraMarkings.markingFrame_oldLabel _ _ _ _ _

/-- Lower the selected power after moving all insertions into the same frame. -/
def lowerAncestorPowers (q : SurfaceAncestorKey X) (hg : q.genus = 0)
    (hp : ¬q.IsPrimary) : ExtraMarkings (extraCount q) (Fin 3) → ℕ :=
  letI := ExtraMarkings.decidableEq (Fin 3) (extraCount q)
  lowerPower (q.orderedPowers ∘ ancestorFrame q hg hp)
    (ExtraMarkings.oldLabel (extraCount q) (0 : Fin 3))

/-- The selected power is positive, so the lowered monomial recovers the input. -/
theorem lowerAncestorPowers_restore (q : SurfaceAncestorKey X) (hg : q.genus = 0)
    (hp : ¬q.IsPrimary) :
    letI := ExtraMarkings.decidableEq (Fin 3) (extraCount q)
    lowerAncestorPowers q hg hp + Pi.single (ExtraMarkings.oldLabel (extraCount q) (0 : Fin 3)) 1 =
      q.orderedPowers ∘ ancestorFrame q hg hp := by
  letI := ExtraMarkings.decidableEq (Fin 3) (extraCount q)
  funext s
  by_cases hs : s = ExtraMarkings.oldLabel (extraCount q) (0 : Fin 3)
  · subst s
    simp only [lowerAncestorPowers, lowerPower, Pi.add_apply, Function.update_self,
      Pi.single_eq_same, Function.comp_apply, ancestorFrame_old]
    exact Nat.sub_add_cancel (q.positiveMark_pos hp)
  · simp only [lowerAncestorPowers, lowerPower, Pi.add_apply,
      Function.update_of_ne hs, Pi.single_eq_of_ne hs, add_zero]

/-- Every component of a one-step contraction has smaller total cotangent degree. -/
theorem sum_lowerAncestorPowers_lt (q : SurfaceAncestorKey X) (hg : q.genus = 0)
    (hp : ¬q.IsPrimary) : (∑ s, lowerAncestorPowers q hg hp s) < q.totalPsi := by
  letI := ExtraMarkings.decidableEq (Fin 3) (extraCount q)
  have hrestore := congrArg (fun k : ExtraMarkings (extraCount q) (Fin 3) → ℕ ↦ ∑ s, k s)
    (lowerAncestorPowers_restore q hg hp)
  simp only [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply,
    Equiv.sum_comp] at hrestore
  rw [q.sum_orderedPowers] at hrestore
  omega

/-- One actual psi-boundary equation, evaluated with explicit component values. -/
def ancestorStep (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusZeroTerms 0 (extraCount q)).map fun t ↦
    t.1 * t.2.surfaceEval X
      (fun g S _ h beta k a ↦ next (SurfaceAncestorKey.ofLabels g S h beta k a))
      q.beta (lowerAncestorPowers q hg hp) (q.orderedLabels ∘ ancestorFrame q hg hp)).sum

/-- The step only inspects genus-zero ancestor values of strictly smaller degree. -/
theorem ancestorStep_congr (v w : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hp : ¬q.IsPrimary)
    (hv : ∀ q' : SurfaceAncestorKey X, q'.genus = 0 → q'.totalPsi < q.totalPsi → v q' = w q') :
    ancestorStep v q hg hp = ancestorStep w q hg hp := by
  unfold ancestorStep
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  congr 1
  apply t.2.surfaceEval_congr_of_bounds
  intro g S _ h beta k a hgen hdegree
  apply hv (SurfaceAncestorKey.ofLabels g S h beta k a) (Nat.eq_zero_of_le_zero hgen)
  rw [SurfaceAncestorKey.totalPsi_ofLabels]
  exact hdegree.trans_lt (sum_lowerAncestorPowers_lt q hg hp)

/-- Structural fuel recursion; nonzero outputs are interpreted only in genus zero.
The public evaluator below supplies enough fuel for every recursive dependency. -/
def ancestorValueFuel (X : SurfaceTarget) : ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => if q.genus = 0 ∧ q.IsPrimary then primaryValue X q.beta q.primaryLabels else 0
  | fuel+1, q => if hg : q.genus = 0 then
      if hp : q.IsPrimary then primaryValue X q.beta q.primaryLabels
      else ancestorStep (ancestorValueFuel X fuel) q hg hp
    else 0

/-- Total genus-zero ancestor evaluator, at arbitrary stable marking count and full class. -/
def ancestorValue (X : SurfaceTarget) (q : SurfaceAncestorKey X) : ℚ :=
  ancestorValueFuel X q.totalPsi q

/-- Increasing an already sufficient fuel bound cannot change the result. -/
theorem ancestorValueFuel_stable (fuel more : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 0) (hf : q.totalPsi ≤ fuel) (hm : q.totalPsi ≤ more) :
    ancestorValueFuel X fuel q = ancestorValueFuel X more q := by
  induction fuel generalizing more q with
  | zero =>
      have hp := q.totalPsi_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hf)
      cases more with
      | zero => rfl
      | succ more => rw [ancestorValueFuel, if_pos ⟨hg, hp⟩,
          ancestorValueFuel, dif_pos hg, dif_pos hp]
  | succ fuel ih =>
      by_cases hp : q.IsPrimary
      · cases more with
        | zero =>
            symm
            rw [ancestorValueFuel, if_pos ⟨hg, hp⟩,
              ancestorValueFuel, dif_pos hg, dif_pos hp]
        | succ more => rw [ancestorValueFuel, dif_pos hg, dif_pos hp,
            ancestorValueFuel, dif_pos hg, dif_pos hp]
      · cases more with
        | zero => exact (hp (q.totalPsi_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hm))).elim
        | succ more =>
            rw [ancestorValueFuel, dif_pos hg, dif_neg hp,
              ancestorValueFuel, dif_pos hg, dif_neg hp]
            apply ancestorStep_congr
            intro q' hg' hdegree
            exact ih more q' hg' (by omega) (by omega)

section Soundness
variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (P : PsiClasses C)
  (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (J : GluingForgetfulCompatibility F N) (K : PsiForgetFormula P)
  (hK : PsiBoundaryExpansion.TailCompatible K F N)
  (hterms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
  (hpairing : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)

include Z F N J K hK hterms hpairing

/-- The numerical step is derived from the original class-level cotangent law,
primitive forgetting/gluing compatibility and the actual surface metric. -/
theorem ancestorStep_eval (q : SurfaceAncestorKey X) (hg : q.genus = 0) (hp : ¬q.IsPrimary) :
    ancestorStep (SurfaceAncestorKey.eval Omega P I) q hg hp = q.eval Omega P I := by
  letI := ExtraMarkings.decidableEq (Fin 3) (extraCount q)
  have hstep := PsiBoundaryExpansion.genusZero_ancestor_eq_contractions Z F N J Omega P K hK
    0 (extraCount q) (hterms (extraCount q)) q.beta (lowerAncestorPowers q hg hp)
      (fun s ↦ (q.orderedLabels (ancestorFrame q hg hp s)).value)
  rw [lowerAncestorPowers_restore] at hstep
  have hzero : StableArity 0 (Fin q.orderedInsertions.length) := by
    rw [StableArity, Fintype.card_fin, Nat.mul_zero, Nat.zero_add]
    exact three_le_length q hg
  have hr := congrArg (fun f ↦ f (fun s ↦ (q.orderedLabels s).value))
    (Omega.ancestorInvariant_relabel P I 0 (ExtraMarkings (extraCount q) (Fin 3))
      (Fin q.orderedInsertions.length) (StableArity.zero_fin_three.extraMarkings (extraCount q))
      hzero (ancestorFrame q hg hp) q.beta (q.orderedPowers ∘ ancestorFrame q hg hp))
  simp only [MultilinearMap.domDomCongr_apply, Function.comp_apply,
    Equiv.apply_symm_apply] at hr
  have hq : SurfaceAncestorKey.ofLabels 0 (Fin q.orderedInsertions.length) hzero q.beta
      q.orderedPowers q.orderedLabels = q := by
    apply (SurfaceAncestorKey.eq_iff _ _).mpr
    refine ⟨hg.symm, rfl, ?_⟩
    have he := congrArg SurfaceAncestorKey.insertions q.of_ordered_eq
    exact he
  have hi := SurfaceAncestorKey.eval_ofLabels Omega P I 0 _ hzero q.beta
    q.orderedPowers q.orderedLabels
  rw [hq] at hi
  rw [ancestorStep]
  calc
    _ = ((PsiBoundaryExpansion.genusZeroTerms 0 (extraCount q)).map fun t ↦
        (algebraMap ℚ ℚ t.1) * t.2.gwAncestorContraction Omega P I q.beta
          (lowerAncestorPowers q hg hp)
          (fun s ↦ (q.orderedLabels (ancestorFrame q hg hp s)).value)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      simp only [SurfaceAncestorKey.eval_ofLabels, Algebra.algebraMap_self_apply]
      rw [t.2.surfaceEval_eq_gwAncestorContraction Omega P I hpairing]
      rfl
    _ = _ := hstep.symm.trans (hr.trans hi.symm)

include U

/-- Sufficient fuel gives the actual ancestor value; every recursive call is
justified by strict cotangent-degree decrease, independently of curve energy. -/
theorem ancestorValueFuel_eq_eval
    (hprimary : ∀ beta m, primaryValue X beta m = SurfacePrimary.eval U 0 beta m)
    (fuel : ℕ) (q : SurfaceAncestorKey X) (hg : q.genus = 0) (hf : q.totalPsi ≤ fuel) :
    ancestorValueFuel X fuel q = q.eval Omega P I := by
  induction fuel generalizing q with
  | zero =>
      have hp := q.totalPsi_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hf)
      rw [ancestorValueFuel, if_pos ⟨hg, hp⟩, q.eval_eq_primary U P hp, hg, hprimary]
  | succ fuel ih =>
      rw [ancestorValueFuel, dif_pos hg]
      by_cases hp : q.IsPrimary
      · rw [dif_pos hp, q.eval_eq_primary U P hp, hg, hprimary]
      · rw [dif_neg hp]
        apply Eq.trans (ancestorStep_congr _ (SurfaceAncestorKey.eval Omega P I) q hg hp ?_)
          (ancestorStep_eval P Z F N J K hK hterms hpairing q hg hp)
        intro q' hg' hdegree
        exact ih q' hg' (by omega)

end Soundness

/-- All stable genus-zero ancestors are reconstructed from the original WDVV
and cotangent geometry and the unchanged finite line/exceptional seed package. -/
theorem ancestorValue_eq_eval {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
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
    (P : PsiClasses C) (K : PsiForgetFormula P)
    (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (hterms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (q : SurfaceAncestorKey X) (hg : q.genus = 0) :
    ancestorValue X q = q.eval Omega P I :=
  ancestorValueFuel_eq_eval U P Z F N J K hK hterms T.pairing_eq
    (primaryValue_eq_eval Z I F N J hsource hboundary p hp Omega P T U laws H hpair
      hline hE houtput) q.totalPsi q hg le_rfl

end AxiomaticGW.SurfaceGenusZero
