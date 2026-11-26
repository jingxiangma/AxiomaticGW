/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroAncestors
public import AxiomaticGW.Surfaces.GenusOneReconstruction

/-!
# Genus-one ancestor reconstruction at arbitrary marking count

The existing genus-one psi expansion starts with the raw loop coefficient
1/24 and adds separating tails. After lowering a selected positive power,
every component has smaller total cotangent degree and genus at most one.
Rational components use the proved genus-zero evaluator; only elliptic
components require recursive values. The primary terminal family is the
existing Getzler reconstruction with its original finite seeds.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne
variable {X : SurfaceTarget}

/-- Markings added to the one-point stable elliptic base. -/
def extraCount (q : SurfaceAncestorKey X) : ℕ := q.orderedInsertions.length - 1

theorem one_le_length (q : SurfaceAncestorKey X) (hg : q.genus = 1) :
    1 ≤ q.orderedInsertions.length := by
  have h := q.stable
  rw [hg, ← q.orderedInsertions_length] at h
  omega

/-- Retained base label zero carries an actual positive cotangent power. -/
def ancestorFrame (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    ExtraMarkings (extraCount q) (Fin 1) ≃ Fin q.orderedInsertions.length :=
  ExtraMarkings.markingFrame 1 _ (one_le_length q hg) 0 (q.positiveMark hp)

theorem ancestorFrame_old (q : SurfaceAncestorKey X) (hg : q.genus = 1)
    (hp : ¬q.IsPrimary) :
    ancestorFrame q hg hp (ExtraMarkings.oldLabel (extraCount q) (0 : Fin 1)) =
      q.positiveMark hp := ExtraMarkings.markingFrame_oldLabel _ _ _ _ _

/-- Lower the selected power in the same frame as all the state insertions. -/
def lowerAncestorPowers (q : SurfaceAncestorKey X) (hg : q.genus = 1)
    (hp : ¬q.IsPrimary) : ExtraMarkings (extraCount q) (Fin 1) → ℕ :=
  letI := ExtraMarkings.decidableEq (Fin 1) (extraCount q)
  lowerPower (q.orderedPowers ∘ ancestorFrame q hg hp)
    (ExtraMarkings.oldLabel (extraCount q) (0 : Fin 1))

theorem lowerAncestorPowers_restore (q : SurfaceAncestorKey X) (hg : q.genus = 1)
    (hp : ¬q.IsPrimary) :
    letI := ExtraMarkings.decidableEq (Fin 1) (extraCount q)
    lowerAncestorPowers q hg hp + Pi.single (ExtraMarkings.oldLabel (extraCount q) (0 : Fin 1)) 1 =
      q.orderedPowers ∘ ancestorFrame q hg hp := by
  letI := ExtraMarkings.decidableEq (Fin 1) (extraCount q)
  funext s
  by_cases hs : s = ExtraMarkings.oldLabel (extraCount q) (0 : Fin 1)
  · subst s
    simp only [lowerAncestorPowers, lowerPower, Pi.add_apply, Function.update_self,
      Pi.single_eq_same, Function.comp_apply, ancestorFrame_old]
    exact Nat.sub_add_cancel (q.positiveMark_pos hp)
  · simp only [lowerAncestorPowers, lowerPower, Pi.add_apply,
      Function.update_of_ne hs, Pi.single_eq_of_ne hs, add_zero]

/-- Every component receives fewer total cotangent powers than the original query. -/
theorem sum_lowerAncestorPowers_lt (q : SurfaceAncestorKey X) (hg : q.genus = 1)
    (hp : ¬q.IsPrimary) : (∑ s, lowerAncestorPowers q hg hp s) < q.totalPsi := by
  letI := ExtraMarkings.decidableEq (Fin 1) (extraCount q)
  have hrestore := congrArg (fun k : ExtraMarkings (extraCount q) (Fin 1) → ℕ ↦ ∑ s, k s)
    (lowerAncestorPowers_restore q hg hp)
  simp only [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply,
    Equiv.sum_comp] at hrestore
  rw [q.sum_orderedPowers] at hrestore
  omega

/-- Rational dependencies are already reconstructed; elliptic values remain explicit. -/
def componentValue (X : SurfaceTarget) (elliptic : SurfaceAncestorKey X → ℚ)
    (q : SurfaceAncestorKey X) : ℚ :=
  if q.genus = 0 then SurfaceGenusZero.ancestorValue X q else elliptic q

/-- Evaluate the original raw loop and separating-tail expansion. -/
def ancestorStep (next : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary) : ℚ :=
  ((PsiBoundaryExpansion.genusOneTerms (extraCount q)).map fun t ↦
    t.1 * t.2.surfaceEval X
      (fun g S _ h beta k a ↦ componentValue X next
        (SurfaceAncestorKey.ofLabels g S h beta k a))
      q.beta (lowerAncestorPowers q hg hp) (q.orderedLabels ∘ ancestorFrame q hg hp)).sum

/-- Only elliptic components of strictly smaller cotangent degree need recursive values. -/
theorem ancestorStep_congr (v w : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hp : ¬q.IsPrimary)
    (hv : ∀ q' : SurfaceAncestorKey X, q'.genus = 1 → q'.totalPsi < q.totalPsi → v q' = w q') :
    ancestorStep v q hg hp = ancestorStep w q hg hp := by
  unfold ancestorStep
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  congr 1
  apply t.2.surfaceEval_congr_of_bounds
  intro g S _ h beta k a hgen hdegree
  by_cases hzero : g = 0
  · simp only [componentValue, SurfaceAncestorKey.ofLabels, hzero, if_pos]
  · simp only [componentValue, SurfaceAncestorKey.ofLabels, if_neg hzero]
    apply hv (SurfaceAncestorKey.ofLabels g S h beta k a) (by change g = 1; omega)
    rw [SurfaceAncestorKey.totalPsi_ofLabels]
    exact hdegree.trans_lt (sum_lowerAncestorPowers_lt q hg hp)

/-- Structural recursion in elliptic cotangent degree; other genera are unsupported here. -/
def ancestorValueFuel (X : SurfaceTarget) : ℕ → SurfaceAncestorKey X → ℚ
  | 0, q => if q.genus = 1 ∧ q.IsPrimary then primaryValue X q.beta q.primaryLabels else 0
  | fuel+1, q => if hg : q.genus = 1 then
      if hp : q.IsPrimary then primaryValue X q.beta q.primaryLabels
      else ancestorStep (ancestorValueFuel X fuel) q hg hp
    else 0

/-- All stable genus-one ancestor requests have an explicit sufficient bound. -/
def ancestorValue (X : SurfaceTarget) (q : SurfaceAncestorKey X) : ℚ :=
  ancestorValueFuel X q.totalPsi q

/-- The computed value is independent of any already sufficient fuel bound. -/
theorem ancestorValueFuel_stable (fuel more : ℕ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 1) (hf : q.totalPsi ≤ fuel) (hm : q.totalPsi ≤ more) :
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

/-- The triangular ancestor equations uniquely determine the elliptic family
once their already reconstructed rational and primary dependencies are fixed.
These equations are derived from geometry below, not added as geometric inputs. -/
theorem ancestorValue_unique (v : SurfaceAncestorKey X → ℚ)
    (hprimary : ∀ q : SurfaceAncestorKey X, q.genus = 1 → q.IsPrimary →
      v q = primaryValue X q.beta q.primaryLabels)
    (hstep : ∀ (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hp : ¬q.IsPrimary),
      v q = ancestorStep v q hg hp)
    (q : SurfaceAncestorKey X) (hg : q.genus = 1) : v q = ancestorValue X q := by
  have hf : ∀ (fuel : ℕ) (q : SurfaceAncestorKey X), q.genus = 1 →
      q.totalPsi ≤ fuel → v q = ancestorValueFuel X fuel q := by
    intro fuel
    induction fuel with
    | zero =>
        intro q hg hbound
        have hp := q.totalPsi_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hbound)
        rw [ancestorValueFuel, if_pos ⟨hg, hp⟩]
        exact hprimary q hg hp
    | succ fuel ih =>
        intro q hg hbound
        rw [ancestorValueFuel, dif_pos hg]
        by_cases hp : q.IsPrimary
        · rw [dif_pos hp]
          exact hprimary q hg hp
        · rw [dif_neg hp, hstep q hg hp]
          apply ancestorStep_congr
          intro q' hg' hdegree
          exact ih q' hg' (by omega)
  exact hf q.totalPsi q hg le_rfl

section Soundness
variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (P : PsiClasses C)
  (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (J : GluingForgetfulCompatibility F N) (K : PsiForgetFormula P)
  (hK : PsiBoundaryExpansion.TailCompatible K F N)
  (pPsi : RelationCertificate.Presentation 1 (Fin 1) 2 3)
  (hpPsi : GenusOnePsi.AcceptsExchange pPsi)
  (hpsi : (Z 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
  (hfund : (Z 1 (Fin 1)).map (StrataModule.basis
    (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
  (hrows : ∀ i, (Z 1 (Fin 1)).map
    (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
  (hloop : GenusOnePsi.loopExpression.Compatible Z F N)
  (hterms : ∀ n t, t ∈ PsiBoundaryExpansion.genusOneTerms n → t.2.Compatible Z F N)
  (hpairing : Omega.pairing = (SurfaceCohomology.frobenius X.blowups).pairing)

/-- Rational component identification is discharged by genus-zero reconstruction
in the final theorem, not supplied as a new numerical family. -/
theorem componentValue_eq
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (q : SurfaceAncestorKey X) :
    componentValue X (SurfaceAncestorKey.eval Omega P I) q = q.eval Omega P I := by
  rw [componentValue]
  split_ifs with h
  · exact hzero q h
  · rfl

include Z F N J K hK pPsi hpPsi hpsi hfund hrows hloop hterms hpairing

/-- The original accepted cotangent relation and primitive gluing geometry
identify the numerical step with the actual genus-one ancestor invariant. -/
theorem ancestorStep_eval
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hp : ¬q.IsPrimary) :
    ancestorStep (SurfaceAncestorKey.eval Omega P I) q hg hp = q.eval Omega P I := by
  letI := ExtraMarkings.decidableEq (Fin 1) (extraCount q)
  have hstep := PsiBoundaryExpansion.genusOne_ancestor_eq_contractions Z F N J Omega P K hK
    pPsi hpPsi hpsi hfund hrows hloop (extraCount q) (hterms (extraCount q)) q.beta
      (lowerAncestorPowers q hg hp) (fun s ↦ (q.orderedLabels (ancestorFrame q hg hp s)).value)
  rw [lowerAncestorPowers_restore] at hstep
  have hone : StableArity 1 (Fin q.orderedInsertions.length) := by
    have hn := one_le_length q hg
    simp only [StableArity, Fintype.card_fin]
    omega
  have hr := congrArg (fun f ↦ f (fun s ↦ (q.orderedLabels s).value))
    (Omega.ancestorInvariant_relabel P I 1 (ExtraMarkings (extraCount q) (Fin 1))
      (Fin q.orderedInsertions.length) (GenusOnePsi.stableArity.extraMarkings (extraCount q))
      hone (ancestorFrame q hg hp) q.beta (q.orderedPowers ∘ ancestorFrame q hg hp))
  simp only [MultilinearMap.domDomCongr_apply, Function.comp_apply,
    Equiv.apply_symm_apply] at hr
  have hq : SurfaceAncestorKey.ofLabels 1 (Fin q.orderedInsertions.length) hone q.beta
      q.orderedPowers q.orderedLabels = q := by
    apply (SurfaceAncestorKey.eq_iff _ _).mpr
    refine ⟨hg.symm, rfl, ?_⟩
    have he := congrArg SurfaceAncestorKey.insertions q.of_ordered_eq
    exact he
  have hi := SurfaceAncestorKey.eval_ofLabels Omega P I 1 _ hone q.beta
    q.orderedPowers q.orderedLabels
  rw [hq] at hi
  rw [ancestorStep]
  calc
    _ = ((PsiBoundaryExpansion.genusOneTerms (extraCount q)).map fun t ↦
        (algebraMap ℚ ℚ t.1) * t.2.gwAncestorContraction Omega P I q.beta
          (lowerAncestorPowers q hg hp)
          (fun s ↦ (q.orderedLabels (ancestorFrame q hg hp s)).value)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      simp only [componentValue_eq P hzero, SurfaceAncestorKey.eval_ofLabels,
        Algebra.algebraMap_self_apply]
      rw [t.2.surfaceEval_eq_gwAncestorContraction Omega P I hpairing]
      rfl
    _ = _ := hstep.symm.trans (hr.trans hi.symm)

include U

/-- Strict elliptic degree decrease and the proved rational family suffice for
every fuel bound; the two identifications are closed in the final theorem. -/
theorem ancestorValueFuel_eq_eval
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hprimary : ∀ beta m, primaryValue X beta m = SurfacePrimary.eval U 1 beta m)
    (fuel : ℕ) (q : SurfaceAncestorKey X) (hg : q.genus = 1) (hf : q.totalPsi ≤ fuel) :
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
          (ancestorStep_eval P Z F N J K hK pPsi hpPsi hpsi hfund hrows hloop hterms hpairing
            hzero q hg hp)
        intro q' hg' hdegree
        exact ih q' hg' (by omega)

end Soundness

/-- Every stable genus-one ancestor follows from the original WDVV/Getzler
inputs, the accepted psi relation and the unchanged finite low-genus seeds. -/
theorem ancestorValue_eq_eval {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility F N)
    (hWsource : ∀ i, (WDVV.expression i).Compatible Z F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible Z F N)
    (GG : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (Z 1 (Fin 4)).map (GetzlerGraphs.cycle x) = GG.cycle x)
    (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
    (hpG : GetzlerGraphs.AcceptsExchange pG)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (pPsi : RelationCertificate.Presentation 1 (Fin 1) 2 3)
    (hpPsi : GenusOnePsi.AcceptsExchange pPsi)
    (hpsi : (Z 1 (Fin 1)).LegPsiCompatible P GenusOnePsi.stableArity)
    (hfund : (Z 1 (Fin 1)).map (StrataModule.basis
      (TautologicalStratum.fundamental 1 (Fin 1) GenusOnePsi.stableArity)) = 1)
    (hrows : ∀ i, (Z 1 (Fin 1)).map
      (RelationCertificate.interpret GenusOnePsi.columns (GenusOnePsi.rows i)) = 0)
    (hloop : GenusOnePsi.loopExpression.Compatible Z F N)
    (hzeroTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
    (honeTerms : ∀ n t, t ∈ PsiBoundaryExpansion.genusOneTerms n → t.2.Compatible Z F N)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
    (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (q : SurfaceAncestorKey X) (hg : q.genus = 1) :
    ancestorValue X q = q.eval Omega P I :=
  ancestorValueFuel_eq_eval U P Z F N J K hK pPsi hpPsi hpsi hfund hrows hloop honeTerms
    T.pairing_eq
    (SurfaceGenusZero.ancestorValue_eq_eval U T laws H hpair Z F N J hWsource hboundary pW hpW
      P K hK hzeroTerms hline hEzero hWoutput)
    (primaryValue_eq_eval Z I F N J hWsource hboundary pW hpW hGsource GG hcycle pG hpG
      Omega P T U laws H hpair hline hEzero hH hE hWoutput hGoutput)
    q.totalPsi q hg le_rfl

end AxiomaticGW.SurfaceGenusOne
