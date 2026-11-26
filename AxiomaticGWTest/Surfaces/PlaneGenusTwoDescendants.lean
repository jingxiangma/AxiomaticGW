import AxiomaticGW.Surfaces.PlaneGenusTwoDescendants
import AxiomaticGW.Tautological.Fixtures.GenusOnePsiReplay
import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiSquareReplay
import AxiomaticGW.Tautological.Fixtures.GenusTwoPsiProductReplay
import AxiomaticGW.Tautological.Fixtures.BelorousskiPandharipandeReplay
import AxiomaticGWTest.Tautological.WDVVReplay
import AxiomaticGWTest.Tautological.GetzlerReplay

open AxiomaticGW BelorousskiPandharipande RelationCertificate PsiBoundaryExpansion
attribute [local instance] strataRealizationModule

private def key (ins : List (SurfaceInsertion .plane)) : SurfaceAncestorKey .plane :=
  ⟨2, 0, ins, by omega⟩

private def initialTable : ℕ → Fin 3 → ℚ := fun _ ↦ ![0, -1 / 960, 0]

private theorem initial_checked : planeCheckCanonicalTable 0 initialTable = true := by
  decide +kernel

-- These higher-power values use a certified terminal table, hence agree with
-- the complete algorithm rather than a separately supplied low-psi family.
set_option maxRecDepth 20000 in
private theorem product_value :
    planeAncestorValue (key [⟨.hyperplane, 1⟩, ⟨.unit, 1⟩]) = -1 / 320 := by
  rw [← planeAncestorValueWith_eq 0 initialTable initial_checked _ rfl (by decide)]
  decide +kernel

set_option maxRecDepth 20000 in
private theorem square_value : planeAncestorValue (key [⟨.unit, 2⟩]) = 7 / 640 := by
  rw [← planeAncestorValueWith_eq 0 initialTable initial_checked _ rfl (by decide)]
  decide +kernel

-- A held mixed expression checks the occurrence adapter before evaluating ancestors.
private theorem query_from_zero_terms (ins : List (SurfaceInsertion .plane))
    (ht : SurfaceQuery.ancestorTerms (⟨2, 0, ins⟩ : SurfaceQuery .plane)
      (by simp only [StableArity]; omega) = RationalTerms.term 1 {key ins}) :
    planeQueryValue? ⟨2, 0, ins⟩ = some (planeAncestorValue (key ins)) := by
  rw [planeQueryValue?, if_pos rfl, planeDescendantValue]
  change some (RationalTerms.eval planeAncestorValue
    (SurfaceQuery.ancestorTerms (⟨2, 0, ins⟩ : SurfaceQuery .plane) _)) = _
  rw [ht]
  simp only [RationalTerms.eval_term, map_one, Multiset.map_singleton,
    Multiset.prod_singleton, one_mul]

example : planeQueryValue? ⟨2, 0, [⟨.hyperplane, 1⟩, ⟨.unit, 1⟩]⟩ = some (-1 / 320) := by
  rw [query_from_zero_terms _ (by decide +kernel), product_value]

example : planeQueryValue? ⟨2, 0, [⟨.unit, 2⟩]⟩ = some (7 / 640) := by
  rw [query_from_zero_terms _ (by decide +kernel), square_value]

-- Reordering moves powers with their states and preserves every occurrence.
example : planeQueryValue? ⟨2, 0, [⟨.unit, 1⟩, ⟨.hyperplane, 1⟩]⟩ = some (-1 / 320) := by
  rw [query_from_zero_terms _ (by decide +kernel)]
  rw [show key [⟨.unit, 1⟩, ⟨.hyperplane, 1⟩] =
    key [⟨.hyperplane, 1⟩, ⟨.unit, 1⟩] by decide +kernel, product_value]

-- Empty genus-two markings are geometric even at degree zero; dimension gives zero.
example : planeQueryValue? ⟨2, 0, []⟩ = some 0 := by
  rw [query_from_zero_terms _ (by decide +kernel)]
  rw [← planeAncestorValueWith_eq 0 initialTable initial_checked _ rfl (by decide)]
  decide +kernel

-- Unsupported genera are rejected before any reconstruction is performed.
example : planeQueryValue? ⟨0, ![1], []⟩ = none := rfl
example : planeQueryValue? ⟨3, 0, [⟨.unit, 2⟩]⟩ = none := rfl

-- Bounded table substitution applies uniformly, not just to the examples above.
example (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (h : planeCheckCanonicalTable bound values = true)
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hb : q.beta 0 ≤ bound) :
    planeAncestorValueWith values q = planeAncestorValue q :=
  planeAncestorValueWith_eq bound values h q hg hb

-- The public theorem consumes the actual six exported relation presentations.
-- Every remaining parameter is original geometry or one of the three finite seeds.
example
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
    (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible Z F N)
    (GG : GetzlerRelationGeometry C)
    (hcycle : ∀ x, (Z 1 (Fin 4)).map (GetzlerGraphs.cycle x) = GG.cycle x)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
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
  (hcP : ∀ b, GenusTwoPsiProduct.SourceCompatible Z F b)
  (hinteriorP : ∀ i : Fin 10, (Z 2 (Fin 2)).map
    (interpret GenusTwoPsiProduct.columns
      (GenusTwoPsiProduct.rows (Fin.castAdd 3 i))) = 0)
  (hinP : ∀ t ∈ GenusTwoPsiProduct.cotangentRelation,
    t.2.expression.Compatible Z F N ∧ t.2.expression.CotangentCompatible Z P)
  (houtP : ∀ n t, t ∈ GenusTwoPsiProduct.cotangentRelation → ∀ z ∈ t.2.addMarkings n,
    z.2.expression.Compatible Z F N ∧ z.2.expression.CotangentCompatible Z P)
    (q : SurfaceQuery .plane) (hg : q.genus = 2) :
    planeQueryValue? q = q.checkedEval U :=
  planeQueryValue?_eq_checkedEval U P T laws H hpair Z F N J hWsource hboundary
    WDVVReplay.presentation WDVVReplay.accepted hGsource GG hcycle
    GetzlerReplay.presentation GetzlerReplay.accepted K hK
    GenusOnePsiReplay.presentation GenusOnePsiReplay.accepted hpsi hfund hrows hloop
    hzeroTerms honeTerms hline hH hWoutput hGoutput HF
    BelorousskiPandharipandeReplay.exchange BelorousskiPandharipandeReplay.accepted
    hlB hcB hinterior hsource hglue hcotangent RT hout hHtwo
    GenusTwoPsiSquareReplay.exchange GenusTwoPsiSquareReplay.accepted
    hELS hLBS hUAS hinteriorS hinS houtS
    GenusTwoPsiProductReplay.exchange GenusTwoPsiProductReplay.accepted
    hcP hinteriorP hinP houtP q hg
