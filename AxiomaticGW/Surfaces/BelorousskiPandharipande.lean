/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoTerms
public import AxiomaticGW.Tautological.BelorousskiPandharipandeForgetful
public import AxiomaticGW.Tautological.BelorousskiPandharipandeCoefficients

/-!
# Complete BP equations for the three fixed surfaces

The twenty published diagrams, six original marking assignments and signed
decorated pullbacks are expanded into the existing exact rational term format.
After the proved lower-genus reconstruction only an affine genus-two system
remains. No pivot, genus-two seed, or uniqueness theorem is assumed here.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open GluingExpression RelationCertificate PsiBoundaryExpansion

/-- Full surface BP polynomial, with an explicit substitution at each component. -/
def surfaceTerms {σ : Type*} (X : SurfaceTarget)
    (vertex : SurfaceVertexValues X (RationalTerms σ)) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms σ :=
  ∑ i, RationalTerms.scale (rawPaperCoefficient i) (∑ e,
    ((orbitCotangentTerm i e).addMarkings n).bind fun t ↦ RationalTerms.scale (t.1 : ℚ)
      (t.2.expression.surfaceDecoratedTerms X vertex t.2.decoration beta k a))

/-- Interpretation preserves every original coefficient, sign and repeated placement. -/
theorem eval_surfaceTerms {σ A : Type*} [CommRing A] [Algebra ℚ A]
    (v : σ → A) (X : SurfaceTarget) (vertex : SurfaceVertexValues X (RationalTerms σ))
    (n : ℕ) (beta : X.Curve) (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms.eval v (surfaceTerms X vertex n beta k a) =
      ∑ i, algebraMap ℚ A (paperCoefficient i * paperNormalization i) * ∑ e,
        (((orbitCotangentTerm i e).addMarkings n).map fun t ↦ algebraMap ℚ A (t.1 : ℚ) *
          t.2.expression.surfaceDecoratedEval X
            (fun g S _ h beta k a ↦ RationalTerms.eval v (vertex g S h beta k a))
            t.2.decoration beta k a).sum := by
  have hbind {ι : Type 1} (s : Multiset ι) (f : ι → RationalTerms σ) :
      RationalTerms.eval v (s.bind f) = (s.map (fun i ↦ RationalTerms.eval v (f i))).sum := by
    simp only [RationalTerms.eval, Multiset.map_bind, Multiset.sum_bind]
  simp only [surfaceTerms, rawPaperCoefficient_eq, RationalTerms.eval_sum, RationalTerms.eval_scale,
    hbind, GluingExpression.eval_surfaceDecoratedTerms]

/-- Dimension reduction and the existing genera-zero/one algorithms, with no genus-two oracle. -/
def genusTwoTerms (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  surfaceTerms X (SurfaceGenusTwo.vertexTerms X) n beta k a

/-- Affine support and effective full-class remainders hold at every marking count and power. -/
theorem genusTwoTerms_bound (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (k : ExtraMarkings n (Fin 3) → ℕ) (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    SurfaceGenusTwo.TermsBound 2 beta (genusTwoTerms X n beta k a) := by
  unfold genusTwoTerms surfaceTerms
  apply SurfaceGenusTwo.termsBound_sum
  intro i _
  apply SurfaceGenusTwo.termsBound_scale
  apply SurfaceGenusTwo.termsBound_sum
  intro e _
  apply SurfaceGenusTwo.termsBound_bind
  intro t _
  apply SurfaceGenusTwo.termsBound_scale
  exact SurfaceGenusTwo.termsBound_decorated t.2.expression t.2.decoration beta k a

attribute [local instance] strataRealizationModule

/-- Vanishing of the concrete surface equation is derived from the original
BP sources and the primitive gluing/forgetful laws. The lower-genus
identifications are discharged by the existing finite-seed reconstruction
theorems; they are not new relation or genus-two numerical assumptions. -/
theorem eval_genusTwoTerms_eq_zero {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
    {I : StableCurveIntegration C}
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
    (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
    (K : PsiForgetFormula P) (hK : TailCompatible K F N) (H : TailForgetCompatible C)
    (G : GluingForgetfulCompatibility F N)
    (p : Exchange) (hp : AcceptsExchange p)
    (hl : ∀ e, (Z 2 (Fin 3)).RelabelCompatible (Z 2 (Fin 3))
      stableArity stableArity (labelPermutation e))
    (hc : ∀ b, SourceMapCompatible Z F b)
    (hinterior : ∀ i : Fin 4, (Z 2 (Fin 3)).map
      (interpret columns (unsymmetrizedRows (Fin.castAdd 16 i))) = 0)
    (hsource : ∀ i, (Z (sourceGenus (sourceFamily i)) (Fin (sourceArity (sourceFamily i)))).map
      (sourceExpression i) = 0)
    (hglue : ∀ i e, (orbitTerm i e).1.Compatible Z F N)
    (hcotangent : ∀ i e, (orbitTerm i e).1.CotangentCompatible Z P)
    (hzero : ∀ q : SurfaceAncestorKey X, q.genus = 0 →
      SurfaceGenusZero.ancestorValue X q = q.eval Omega P I)
    (hone : ∀ q : SurfaceAncestorKey X, q.genus = 1 →
      SurfaceGenusOne.ancestorValue X q = q.eval Omega P I)
    (n : ℕ) (hout : ∀ i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (genusTwoTerms X n beta k a) = 0 := by
  have he := gw_forget_relation_from_generators Z F N Omega P K hK H G p hp hl hc
    hinterior hsource hglue hcotangent n hout beta k (fun s ↦ (a s).value)
  rw [genusTwoTerms, eval_surfaceTerms]
  simp only [SurfaceGenusTwo.vertexTerms, SurfaceGenusTwo.eval_residualTerms P T hzero hone,
    SurfaceAncestorKey.eval_ofLabels,
    GluingExpression.surfaceDecoratedEval_eq_gwDecoratedAncestorContraction Omega P I
      T.pairing_eq, Algebra.algebraMap_self_apply]
  simpa only [Rat.smul_def, Rat.cast_id, zsmul_eq_mul] using he

/-- The complete affine BP equation follows from named geometric laws, the
accepted original relation certificates and the unchanged finite low-genus
seeds. Every genus-zero/one component value is derived here. The remaining
variables are actual genus-two ancestors, whose coupled system still needs
additional reduction and invertibility arguments. -/
theorem eval_genusTwoTerms_eq_zero_from_geometry {X : SurfaceTarget}
    {C : StableCurveCohomology ℚ}
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
    (n : ℕ) (hout : ∀ i e t, t ∈ (orbitCotangentTerm i e).addMarkings n →
      t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
    (beta : X.Curve) (k : ExtraMarkings n (Fin 3) → ℕ)
    (a : ExtraMarkings n (Fin 3) → SurfaceBasisLabel X) :
    RationalTerms.eval (SurfaceAncestorKey.eval Omega P I) (genusTwoTerms X n beta k a) = 0 := by
  exact eval_genusTwoTerms_eq_zero Z F N Omega P T K hK HF J pB hpB hlB hcB
    hinterior hsource hglue hcotangent
    (SurfaceGenusZero.ancestorValue_eq_eval U T laws H hpair Z F N J hWsource hboundary pW hpW
      P K hK hzeroTerms hline hEzero hWoutput)
    (SurfaceGenusOne.ancestorValue_eq_eval U P T laws H hpair Z F N J hWsource hboundary pW hpW
      hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms honeTerms
      hline hEzero hH hE hWoutput hGoutput) n hout beta k a

end AxiomaticGW.BelorousskiPandharipande
