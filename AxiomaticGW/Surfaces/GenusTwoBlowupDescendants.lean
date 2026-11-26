/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorGeometry
public import AxiomaticGW.Surfaces.GenusTwoBlowupLowPsi
public import AxiomaticGW.Surfaces.MixedAncestorReduction
public import AxiomaticGW.Surfaces.GenusZeroFullDescendants

/-!
# Genus-two descendants on the blowups at every finite arity

The existing square/product ancestor reduction terminates at the reconstructed
low-power family. That terminal family retains the entire signed calibration
polynomial on all effective subclasses. Mixed cotangent reduction then converts
every finite descendant query, including class zero and empty markings, to the
ancestor algorithm. No plane-specific calibration cancellation is used.

The interpretation below uses the original unsolved BP/L24 equations, the
original square/product geometric generators, finite low-genus and divisor
seeds, and named exceptional support and cotangent geometry. It neither takes
an ancestor/descendant value oracle nor assumes the desired solved recurrence.
The geometric producers of BP/L24 remain separate reusable theorems.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwoBlowupDescendants
open RelationCertificate PsiBoundaryExpansion
variable {X : SurfaceTarget}

/-- All finite ancestors use the reconstructed full low-power normalization. -/
def ancestorValue (i : Fin X.blowups) (q : SurfaceAncestorKey X) : ℚ :=
  SurfaceGenusTwo.ancestorValue (SurfaceGenusTwoBlowupLowPsi.ancestorValue i) q

/-- Reuse a canonical table without altering any low-power calibration tail. -/
def ancestorValueWith (values : SurfaceGenusTwoBlowupOrder.State X → ℚ)
    (q : SurfaceAncestorKey X) : ℚ :=
  SurfaceGenusTwo.ancestorValue (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith values) q

/-- A canonical table that agrees through an energy bound computes all ancestors in that range.
Every calibration tail and psi-reduction dependency remains within the same full-class bound. -/
theorem ancestorValueWith_eq_of_table (i : Fin X.blowups) (bound : ℕ)
    (values : SurfaceGenusTwoBlowupOrder.State X → ℚ)
    (hcheck : ∀ s : SurfaceGenusTwoBlowupOrder.State X, X.effective.energy s.1 ≤ bound →
      values s = SurfaceGenusTwoBlowupRecursion.values i s)
    (q : SurfaceAncestorKey X) (hg : q.genus = 2)
    (hb : X.effective.energy q.beta ≤ bound) :
    ancestorValueWith values q = ancestorValue i q := by
  apply SurfaceGenusTwo.ancestorValue_congr _ _ bound _ q hg hb
  intro r hgen hpsi hbound
  apply SurfaceGenusTwoBlowupLowPsi.ancestorValueWith_congr _ _ r hgen hpsi
  intro beta hsplit family
  obtain ⟨delta, hdelta⟩ := hsplit
  have he := congrArg X.effective.energy hdelta
  rw [map_add] at he
  exact hcheck (beta, family) (by dsimp only; omega)

/-- Basis descendants at every numbered arity, including zero. -/
def descendantValue (i : Fin X.blowups) (n : ℕ) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.eval (ancestorValue i)
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin n)
      (by simp only [StableArity, Fintype.card_fin]; omega)
      (List.finRange n) beta d 0 a)

/-- Retain every ordered insertion and power; other genera are outside this evaluator. -/
def queryValue? (i : Fin X.blowups) (q : SurfaceQuery X) : Option ℚ :=
  if q.genus = 2 then
    some (descendantValue i q.insertions.length q.beta
      (fun j ↦ (q.insertions.get j).psi) (fun j ↦ (q.insertions.get j).label))
  else none

/-- Sorted occurrence frames evaluate basis states on any finite marking type. -/
def basisValue (i : Fin X.blowups) (S : Type) [Fintype S] (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) : ℚ :=
  let q := SurfaceAncestorKey.ofLabels 2 S (by simp only [StableArity]; omega) beta k a
  descendantValue i q.orderedInsertions.length beta q.orderedPowers q.orderedLabels

/-- Multilinear basis expansion handles arbitrary cohomology states at every finite arity. -/
def stateValue (i : Fin X.blowups) (S : Type) [Fintype S] [DecidableEq S]
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) : ℚ :=
  ∑ b : S → SurfaceBasisLabel X, let w := ∏ s, (b s).coordinate (a s)
    if w = 0 then 0 else w * basisValue i S beta k b

section Geometry
attribute [local instance] strataRealizationModule

variable
    (i : Fin X.blowups)
  {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups)
      X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I)
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
    (hEzero : ∀ j, (SurfaceSeed.exceptional j : SurfaceSeed X).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U =
      -1 / 8)
    (hEone : ∀ j, (SurfaceSeed.genusOneExceptional j : SurfaceSeed X).query.eval U =
      -1 / 24)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (HF : TailForgetCompatible C)
    (V : StableMapIntersection U) (hV : ExceptionalPointSupport V)
    {St : StableMapStabilization V} (RT : RationalTailIntersection V St P)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed X).query.eval U = -1 / 960)
    (hEtwo : ∀ j, (SurfaceSeed.genusTwoExceptional j : SurfaceSeed X).query.eval U =
      -1 / 2880)
    (hBP : ∀ n beta a, RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
      (SurfaceGenusTwoBlowupNRelation.bpRow X n beta a) = 0)
    (hL : ∀ n beta (a : Fin 4 → SurfaceBasisLabel X),
      RationalTerms.eval (SurfacePolynomialReduction.variableEval U P)
        (L24Relation.normalizedGenusTwoTerms X n beta 0
          (SurfaceGenusZero.pointLabels a n)) = 0)

include i U P T laws H hpair Z F N J hWsource hboundary
  pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
  honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo hBP hL

variable
  (pS : GenusTwoPsiSquare.Exchange) (hpS : GenusTwoPsiSquare.AcceptsExchange pS)
  (hELS : (Z 1 (Fin 1)).RelabelCompatible (Z 1 (Option (Fin 0)))
    GenusOnePsi.stableArity GenusTwoPsiSquare.ellipticSourceStable (finSuccEquiv 0))
  (hLBS : (Z 1 (Option (Fin 0))).SeparatingCompatible (Z 1 (Option (Fin 1)))
    (Z 2 (Fin 0 ⊕ Fin 1)) F GenusTwoPsiSquare.ellipticSourceStable
      GenusTwoPsiSquare.ellipticMarkedStable)
  (hUAS : (Z 2 (Fin 0 ⊕ Fin 1)).RelabelCompatible (Z 2 (Fin 1))
    GenusTwoPsiSquare.separatingStable GenusTwoPsiSquare.stableArity
      (Equiv.emptySum (Fin 0) (Fin 1)))
  (hinteriorS : ∀ i : Fin 6, (Z 2 (Fin 1)).map
    (interpret GenusTwoPsiSquare.columns (GenusTwoPsiSquare.rows i.castSucc)) = 0)
  (hinS : ∀ t ∈ GenusTwoPsiSquare.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtS : ∀ n t, t ∈ GenusTwoPsiSquare.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
  (pP : GenusTwoPsiProduct.Exchange) (hpP : GenusTwoPsiProduct.AcceptsExchange pP)
  (hcP : ∀ b, GenusTwoPsiProduct.SourceCompatible Z F b)
  (hsourceP : ∀ b,
    (Z (BelorousskiPandharipande.sourceGenus (GenusTwoPsiProduct.sourceFamily b))
      (Fin (BelorousskiPandharipande.sourceArity (GenusTwoPsiProduct.sourceFamily b)))).map
        (BelorousskiPandharipande.sourceExpression (GenusTwoPsiProduct.sourceIndex b)) = 0)
  (hinteriorP : ∀ i : Fin 10, (Z 2 (Fin 2)).map
    (interpret GenusTwoPsiProduct.columns
      (GenusTwoPsiProduct.rows (Fin.castAdd 3 i))) = 0)
  (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtP : ∀ n t, t ∈ GenusTwoPsiProduct.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)

include pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP
  hinteriorP hinP houtP

/-- Original geometric psi generators and reconstructed lower genera identify every ancestor.
The terminal family is proved from the unsolved original BP/L24 equations and finite seeds. -/
theorem ancestorValue_from_original_equations (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) : ancestorValue i q = q.eval Omega P I := by
  apply SurfaceGenusTwo.ancestorValue_eq_of_identifications P T Z F N K hK HF J
    pS hpS hELS hLBS hUAS hinteriorS (hrows 0) hinS houtS pP hpP hcP hsourceP
    hinteriorP hinP houtP
  · exact SurfaceGenusZero.ancestorValue_eq_eval U T laws H hpair Z F N J hWsource hboundary
      pW hpW P K hK hzeroTerms hline hEzero hWoutput
  · exact SurfaceGenusOne.ancestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline hEzero hH hEone hWoutput hGoutput
  · intro r hgen hpower
    exact SurfaceGenusTwoBlowupLowPsi.ancestorValue_from_original_equations i U P T V hV
      hHtwo hEtwo hBP hL laws H hpair Z F N J hWsource hboundary pW hpW hline hEzero
      hWoutput RT r hgen hpower
  · exact hg

/-- Every finite basis descendant follows from the same original source equations and seeds.
Higher calibration coefficients are reconstructed by WDVV and rational-tail geometry. -/
theorem descendantValue_from_original_equations (n : ℕ) (beta : X.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel X) :
    descendantValue i n beta d a = U.invariant 2 (Fin n) beta d (fun s ↦ (a s).value) := by
  have h : StableArity 2 (Fin n) := by
    simp only [StableArity, Fintype.card_fin]
    omega
  rw [descendantValue, SurfaceDescendant.eval_mixedAncestorTerms_congr (ancestorValue i)
    (SurfaceAncestorKey.eval Omega P I) 2 (Fin n) h]
  · rw [SurfaceDescendant.eval_mixedAncestorTerms RT
      (SurfaceDescendant.reconstructedCalibrationMatrix_eq U T laws H hpair Z F N J
        hWsource hboundary pW hpW P hline hEzero hWoutput RT),
      M.mixedInvariant_zero_ancestor, U.invariant_of_stable 2 (Fin n) h]
    intro s hs
    exact False.elim (hs (List.mem_finRange s))
  · intro b e labels
    exact ancestorValue_from_original_equations i U P T laws H hpair Z F N J hWsource
      hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows
      hloop hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT
      hHtwo hEtwo hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP
      hsourceP hinteriorP hinP houtP _ rfl

/-- Queries are answered on their actual geometric domain, including empty degree-zero requests. -/
theorem queryValue?_eq_checkedEval_from_original_equations (q : SurfaceQuery X)
    (hg : q.genus = 2) : queryValue? i q = q.checkedEval U := by
  have hd : q.GeometricDomain := Or.inr (by simp only [StableArity, hg]; omega)
  rw [queryValue?, if_pos hg, SurfaceQuery.checkedEval_of_geometricDomain U q hd]
  congr 1
  rw [SurfaceQuery.eval, hg]
  exact descendantValue_from_original_equations i U P T laws H hpair Z F N J hWsource
    hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows
    hloop hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT
    hHtwo hEtwo hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP
    hsourceP hinteriorP hinP houtP _ _ _ _

/-- Finite marking transport preserves every basis state and cotangent occurrence. -/
theorem basisValue_from_original_equations (S : Type) [Fintype S] (beta : X.Curve)
    (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    basisValue i S beta k a = U.invariant 2 S beta k (fun s ↦ (a s).value) := by
  rw [basisValue, descendantValue_from_original_equations i U P T laws H hpair Z F N J
    hWsource hboundary pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows
    hloop hzeroTerms honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT
    hHtwo hEtwo hBP hL pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP
    hsourceP hinteriorP hinP houtP]
  exact (SurfaceAncestorKey.descendantEval_eq_ordered U
    (SurfaceAncestorKey.ofLabels 2 S (by simp only [StableArity]; omega) beta k a)).symm.trans
      (SurfaceAncestorKey.descendantEval_ofLabels U 2 S _ beta k a)

/-- The same algorithm reconstructs arbitrary cohomology-state descendants,
with no value callback. -/
theorem stateValue_from_original_equations (S : Type) [Fintype S] [DecidableEq S]
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    stateValue i S beta k a = U.invariant 2 S beta k a := by
  rw [stateValue, ← U.invariantMap_apply 2 S beta k a, SurfaceBasisLabel.multilinear_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  split_ifs with hw
  · rw [hw, zero_mul]
  · rw [basisValue_from_original_equations i U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline hEzero hH hEone hWoutput hGoutput HF V hV RT hHtwo hEtwo hBP hL
      pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hsourceP hinteriorP hinP houtP,
      U.invariantMap_apply]

end Geometry
end AxiomaticGW.SurfaceGenusTwoBlowupDescendants
