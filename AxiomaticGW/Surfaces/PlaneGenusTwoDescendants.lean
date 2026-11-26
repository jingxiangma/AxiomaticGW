/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoAncestorGeometry
public import AxiomaticGW.Surfaces.PlaneGenusTwoLowPsi
public import AxiomaticGW.Surfaces.MixedAncestorReduction

/-!
# Plane genus-two descendants at every finite arity

The terminating ancestor recursion uses the reconstructed low-psi plane family.
Mixed cotangent reduction then evaluates stable-map descendants using the
already reconstructed genus-zero calibration. Genus two is curve-stable at
every arity, including zero, so no auxiliary unstable convention is needed.

The final theorems use the original geometric relation and intersection inputs
and exactly the three existing seeds: the rational line, elliptic hyperplane
and genus-two hyperplane values. Neither an ancestor family nor a solved
recurrence is assumed. Numerical certificate coverage is a separate obligation.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open RelationCertificate PsiBoundaryExpansion

/-- All finite plane genus-two ancestors, from the original canonical recursion. -/
def planeAncestorValue (q : SurfaceAncestorKey .plane) : ℚ :=
  SurfaceGenusTwo.ancestorValue planeLowPsiValue q

/-- Reuse a finite canonical table for the low-power terminal values. -/
def planeAncestorValueWith (values : ℕ → Fin 3 → ℚ) (q : SurfaceAncestorKey .plane) : ℚ :=
  SurfaceGenusTwo.ancestorValue (planeLowPsiValueWith values) q

/-- An accepted canonical table computes every ancestor in its degree range,
including arbitrarily many markings and arbitrarily high cotangent powers. -/
theorem planeAncestorValueWith_eq (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (hcheck : planeCheckCanonicalTable bound values = true)
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hb : q.beta 0 ≤ bound) :
    planeAncestorValueWith values q = planeAncestorValue q := by
  have he (beta : SurfaceTarget.plane.Curve) :
      SurfaceTarget.plane.effective.energy beta = 3 * beta 0 := by
    change (∑ i : Fin 1, (![3] : Fin 1 → ℕ) i * beta i) = _
    rw [Fin.sum_univ_one]
    rfl
  refine SurfaceGenusTwo.ancestorValue_congr _ _ (3 * bound) ?_ q hg ?_
  · intro r hgen hpsi hbound
    rw [he] at hbound
    exact planeLowPsiValueWith_eq bound values hcheck r hgen hpsi (by omega)
  · rw [he]
    omega

/-- Exact stable-map descendant evaluation with numbered basis insertions. -/
def planeDescendantValue (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel .plane) : ℚ :=
  RationalTerms.eval planeAncestorValue
    (SurfaceDescendant.mixedAncestorTerms 2 (Fin n)
      (by simp only [StableArity, Fintype.card_fin]; omega)
      (List.finRange n) beta d 0 a)

/-- Preserve the full ordered query; other genera are outside this evaluator. -/
def planeQueryValue? (q : SurfaceQuery .plane) : Option ℚ :=
  if q.genus = 2 then
    some (planeDescendantValue q.insertions.length q.beta
      (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label))
  else none

section Geometry
attribute [local instance] strataRealizationModule

variable
    {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
      SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification SurfaceTarget.plane Omega)
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
    (hline : (SurfaceSeed.line : SurfaceSeed SurfaceTarget.plane).query.eval U = 1)
    (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed SurfaceTarget.plane).query.eval U =
      -1 / 8)
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible Z F N)
    (HF : TailForgetCompatible C)
    (pB : Exchange) (hpB : AcceptsExchange pB)
    (hlB : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hcB : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    {V : StableMapIntersection U} {St : StableMapStabilization V}
    (RT : RationalTailIntersection V St P)
    (hout : ∀ n i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (hHtwo : (SurfaceSeed.genusTwoHyperplane : SurfaceSeed SurfaceTarget.plane).query.eval U =
      -1 / 960)

include U P T laws H hpair Z F N J hWsource hboundary
  pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
  honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
  hglue hcotangent RT hout hHtwo

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
  (hinteriorP : ∀ i : Fin 10, (Z 2 (Fin 2)).map
    (interpret GenusTwoPsiProduct.columns
      (GenusTwoPsiProduct.rows (Fin.castAdd 3 i))) = 0)
  (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtP : ∀ n t, t ∈ GenusTwoPsiProduct.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)

include pS hpS hELS hLBS hUAS hinteriorS hinS houtS pP hpP hcP hinteriorP hinP houtP

/-- The original source equations and finite seeds identify every ancestor.
The square elliptic source and three product sources are reused from the
existing genus-one/BP inputs, rather than assumed again. -/
theorem planeAncestorValue_eq_eval (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) :
    planeAncestorValue q = q.eval Omega P I := by
  apply SurfaceGenusTwo.ancestorValue_eq_of_identifications P T Z F N K hK HF J
    pS hpS hELS hLBS hUAS hinteriorS (hrows 0) hinS houtS pP hpP hcP
    (fun b ↦ hsource (GenusTwoPsiProduct.sourceIndex b)) hinteriorP hinP houtP
  · exact SurfaceGenusZero.ancestorValue_eq_eval U T laws H hpair Z F N J hWsource hboundary
      pW hpW P K hK hzeroTerms hline (fun i ↦ Fin.elim0 i) hWoutput
  · exact SurfaceGenusOne.ancestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline (fun i ↦ Fin.elim0 i) hH (fun i ↦ Fin.elim0 i) hWoutput hGoutput
  · intro r hgen hpower
    exact (planeLowPsiValue_from_geometry U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
      hglue hcotangent RT hout hHtwo r hgen hpower).2
  · exact hg

/-- Every finite basis descendant is determined by the same geometric inputs
and three seeds, using the proved rational-tail comparison and calibration. -/
theorem planeDescendantValue_eq (n : ℕ) (beta : SurfaceTarget.plane.Curve)
    (d : Fin n → ℕ) (a : Fin n → SurfaceBasisLabel .plane) :
    planeDescendantValue n beta d a =
      U.invariant 2 (Fin n) beta d (fun s ↦ (a s).value) := by
  have h : StableArity 2 (Fin n) := by
    simp only [StableArity, Fintype.card_fin]
    omega
  rw [planeDescendantValue, SurfaceDescendant.eval_mixedAncestorTerms_congr planeAncestorValue
    (SurfaceAncestorKey.eval Omega P I) 2 (Fin n) h]
  · rw [SurfaceDescendant.eval_mixedAncestorTerms RT
      (SurfaceDescendant.reconstructedCalibrationMatrix_eq U T laws H hpair Z F N J
        hWsource hboundary pW hpW P hline (fun i ↦ Fin.elim0 i) hWoutput RT),
      M.mixedInvariant_zero_ancestor, U.invariant_of_stable 2 (Fin n) h]
    intro s hs
    exact False.elim (hs (List.mem_finRange s))
  · intro b e labels
    exact planeAncestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
      honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
      hglue hcotangent RT hout hHtwo pS hpS hELS hLBS hUAS hinteriorS hinS houtS
      pP hpP hcP hinteriorP hinP houtP _ rfl

/-- Every genus-two plane query has its actual checked geometric value,
including degree zero, empty insertion lists and dimension-forced zeros. -/
theorem planeQueryValue?_eq_checkedEval (q : SurfaceQuery .plane) (hg : q.genus = 2) :
    planeQueryValue? q = q.checkedEval U := by
  have hd : q.GeometricDomain := Or.inr (by simp only [StableArity, hg]; omega)
  rw [planeQueryValue?, if_pos hg, SurfaceQuery.checkedEval_of_geometricDomain U q hd]
  congr 1
  rw [SurfaceQuery.eval, hg]
  exact planeDescendantValue_eq U P T laws H hpair Z F N J hWsource hboundary
    pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
    honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
    hglue hcotangent RT hout hHtwo pS hpS hELS hLBS hUAS hinteriorS hinS houtS
    pP hpP hcP hinteriorP hinP houtP _ _ _ _

end Geometry

end AxiomaticGW.BelorousskiPandharipande
