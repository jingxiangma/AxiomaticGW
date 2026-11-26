/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneAncestors
public import AxiomaticGW.Surfaces.GenusZeroFullDescendants

/-!
# Genus-one descendants at every finite arity

The mixed ancestor reduction uses the proved genus-one ancestor evaluator and
the existing genus-zero calibration. Sorted marking transport and multilinear
basis expansion provide the stable family required by anticanonical divisor
stabilization. All numerical dependencies are therefore constructed from the
same finite low-genus seeds and explicit geometric contracts.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

/-- Exact genus-one descendant evaluation on any numbered stable marking set. -/
def stableValue (X : SurfaceTarget) (n : ℕ) (hn : 1 ≤ n) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.eval (ancestorValue X)
    (SurfaceDescendant.mixedAncestorTerms 1 (Fin n)
      (by simp only [StableArity, Fintype.card_fin]; omega)
      (List.finRange n) beta d 0 a)

/-- Evaluate the existing ordered query without changing insertion data. -/
def stableQueryValue {X : SurfaceTarget} (q : SurfaceQuery X) (hg : q.genus = 1)
    (h : StableArity q.genus (Fin q.insertions.length)) : ℚ :=
  stableValue X q.insertions.length
    (by simp only [StableArity, hg, Fintype.card_fin] at h; omega)
    q.beta (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label)

/-- Stable basis values on arbitrary finite markings, using a computable sorted frame. -/
def stableBasisValue (X : SurfaceTarget) (S : Type) [Fintype S]
    (h : StableArity 1 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) : ℚ :=
  let q := SurfaceAncestorKey.ofLabels 1 S h beta k a
  stableValue X q.orderedInsertions.length (one_le_length q rfl)
    beta q.orderedPowers q.orderedLabels

/-- Multilinear expansion for the arbitrary states created by divisor reduction.
Zero coefficients are discarded before computing the corresponding basis value. -/
def stableStateValue (X : SurfaceTarget) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity 1 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceCohomology X.blowups) : ℚ :=
  ∑ b : S → SurfaceBasisLabel X, let w := ∏ s, (b s).coordinate (a s)
    if w = 0 then 0 else w * stableBasisValue X S h beta k b

/-- Total numerical evaluation, including the auxiliary zero-class unstable convention. -/
def value (X : SurfaceTarget) (beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S]
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) : ℚ :=
  SurfaceDescendant.stabilizedValue X 1 beta
    (fun S _ _ h k a ↦ stableStateValue X S h beta k a) S k a

/-- Geometric query evaluation; unsupported genera and auxiliary unstable zero
classes return `none`. Stable queries use the direct basis evaluator. -/
def queryValue? {X : SurfaceTarget} (q : SurfaceQuery X) : Option ℚ :=
  letI : Decidable (StableArity q.genus (Fin q.insertions.length)) :=
    inferInstanceAs (Decidable (2 < 2 * q.genus + Fintype.card (Fin q.insertions.length)))
  if hg : q.genus = 1 then
    if h : StableArity q.genus (Fin q.insertions.length) then
      some (stableQueryValue q hg h)
    else if q.beta = 0 then none else
      some (value X q.beta (Fin q.insertions.length)
        (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label.value))
  else none

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (P : PsiClasses C)

/-- Modular composition; the final theorem discharges both family identifications
with the original finite-seed reconstruction results. -/
theorem stableValue_eq_of_identifications
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (Tail : RationalTailIntersection G St P)
    (hcal : ∀ power beta row col,
      SurfaceDescendant.reconstructedCalibrationMatrix X power beta row col =
        row.coordinate (U.calibrationCoefficient power beta col.value))
    (hancestor : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      ancestorValue X q = q.eval Omega P I)
    (n : ℕ) (hn : 1 ≤ n) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) :
    stableValue X n hn beta d a = U.invariant 1 (Fin n) beta d (fun s ↦ (a s).value) := by
  have h : StableArity 1 (Fin n) := by
    simp only [StableArity, Fintype.card_fin]
    omega
  rw [stableValue, SurfaceDescendant.eval_mixedAncestorTerms_congr (ancestorValue X)
    (SurfaceAncestorKey.eval Omega P I) 1 (Fin n) h (fun beta e a ↦ hancestor _ rfl)]
  rw [SurfaceDescendant.eval_mixedAncestorTerms Tail hcal,
    M.mixedInvariant_zero_ancestor, U.invariant_of_stable 1 (Fin n) h]
  intro s hs
  exact False.elim (hs (List.mem_finRange s))

variable (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
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
  {G : StableMapIntersection U} {St : StableMapStabilization G}
  (Tail : RationalTailIntersection G St P)

include T laws H hpair Z F N J hWsource hboundary pW hpW hGsource GG hcycle pG hpG
  K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms hline hEzero hH hE
  hWoutput hGoutput Tail

/-- Stable descendants follow from the original finite seeds, accepted relations,
and explicit cotangent and virtual intersection geometry. -/
theorem stableValue_eq (n : ℕ) (hn : 1 ≤ n) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) :
    stableValue X n hn beta d a = U.invariant 1 (Fin n) beta d (fun s ↦ (a s).value) :=
  stableValue_eq_of_identifications U P Tail
    (SurfaceDescendant.reconstructedCalibrationMatrix_eq U T laws H hpair Z F N J
      hWsource hboundary pW hpW P hline hEzero hWoutput Tail)
    (ancestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary pW hpW
      hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
      hline hEzero hH hE hWoutput hGoutput) n hn beta d a

/-- Stable query interpretation uses the same ordered insertion list. -/
theorem stableQueryValue_eq (q : SurfaceQuery X) (hg : q.genus = 1)
    (h : StableArity q.genus (Fin q.insertions.length)) :
    stableQueryValue q hg h = q.eval U := by
  rw [stableQueryValue, SurfaceQuery.eval, hg]
  exact stableValue_eq U P T laws H hpair Z F N J hWsource hboundary pW hpW
    hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput Tail _ _ _ _ _

theorem stableBasisValue_eq (S : Type) [Fintype S] (h : StableArity 1 S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    stableBasisValue X S h beta k a = U.invariant 1 S beta k (fun s ↦ (a s).value) := by
  rw [stableBasisValue, stableValue_eq U P T laws H hpair Z F N J hWsource hboundary pW hpW
    hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput Tail]
  exact (SurfaceAncestorKey.descendantEval_eq_ordered U
    (SurfaceAncestorKey.ofLabels 1 S h beta k a)).symm.trans
      (SurfaceAncestorKey.descendantEval_ofLabels U 1 S h beta k a)

theorem stableStateValue_eq (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 1 S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    stableStateValue X S h beta k a = U.invariant 1 S beta k a := by
  rw [stableStateValue, ← U.invariantMap_apply 1 S beta k a,
    SurfaceBasisLabel.multilinear_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  split_ifs with hw
  · rw [hw, zero_mul]
  · rw [stableBasisValue_eq U P T laws H hpair Z F N J hWsource hboundary pW hpW
      hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput Tail, U.invariantMap_apply]

/-- The existing proved stabilization bound now reconstructs every genus-one
descendant from the same finite seeds, without a stable-value callback. -/
theorem value_eq (beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S]
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    value X beta S k a = U.invariant 1 S beta k a := by
  apply SurfaceDescendant.stabilizedValue_eq_invariant U T laws H hpair
  intro S _ _ h k a
  rw [stableStateValue_eq U P T laws H hpair Z F N J hWsource hboundary pW hpW
    hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput Tail, U.invariant_of_stable 1 S h]

/-- Every genus-one query is answered exactly on the original geometric domain. -/
theorem queryValue?_eq_checkedEval (q : SurfaceQuery X) (hg : q.genus = 1) :
    queryValue? q = q.checkedEval U := by
  rw [queryValue?, dif_pos hg]
  by_cases h : StableArity q.genus (Fin q.insertions.length)
  · rw [dif_pos h, stableQueryValue_eq U P T laws H hpair Z F N J hWsource hboundary pW hpW
    hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput Tail, SurfaceQuery.checkedEval,
      if_pos (show q.GeometricDomain from Or.inr h)]
  · rw [dif_neg h, SurfaceQuery.checkedEval]
    by_cases hb : q.beta = 0
    · rw [if_pos hb, if_neg]
      exact fun hd ↦ hd.elim (fun hn ↦ hn hb) h
    · rw [if_neg hb, if_pos (show q.GeometricDomain from Or.inl hb),
        value_eq U P T laws H hpair Z F N J hWsource hboundary pW hpW
    hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
    hline hEzero hH hE hWoutput hGoutput Tail, SurfaceQuery.eval, hg]

end AxiomaticGW.SurfaceGenusOne
