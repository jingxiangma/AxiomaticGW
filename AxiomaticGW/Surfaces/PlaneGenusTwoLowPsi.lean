/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.LowPsiDescendant
public import AxiomaticGW.Surfaces.PlaneGenusTwoClaim

/-!
# Plane genus-two values with total cotangent power at most one

Primary and first-descendant normalization reduces arbitrary finite insertion
multisets to the three reconstructed canonical families at the same degree.
A certified finite table can replace the canonical algorithm throughout its
held degree range. No new numerical seed is used. Higher powers still need
the separate genus-two ancestor reduction.
-/

@[expose] public section

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction RelationCertificate PsiBoundaryExpansion

/-- Evaluate low-power normalization against an explicit canonical table.
Its interpretation below requires genus two and total cotangent power at most one. -/
def planeLowPsiValueWith (values : ℕ → Fin 3 → ℚ) (q : SurfaceAncestorKey .plane) : ℚ :=
  RationalTerms.eval (planeCanonicalValuation values) (directNormalizedTerms q)

/-- Reconstruction from the original terminating canonical algorithm. -/
def planeLowPsiValue (q : SurfaceAncestorKey .plane) : ℚ :=
  planeLowPsiValueWith planeCanonicalValues q

/-- Only the canonical triple at the query's exact degree is consulted. -/
theorem planeLowPsiValueWith_congr (v w : ℕ → Fin 3 → ℚ)
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (hv : v (q.beta 0) = w (q.beta 0)) :
    planeLowPsiValueWith v q = planeLowPsiValueWith w q := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  obtain ⟨j, hj⟩ := normalizedTerms_plane_canonical_support q hg hk
    (show t ∈ normalizedTerms q by rwa [normalizedTerms_plane_eq_direct])
  rw [hj, Multiset.mem_singleton] at hx
  subst x
  rw [planeCanonicalValuation_apply, planeCanonicalValuation_apply]
  exact congrFun hv j

/-- Every accepted bounded table also evaluates all low-power insertion
multisets in its range, not only the three displayed canonical queries. -/
theorem planeLowPsiValueWith_eq (bound : ℕ) (values : ℕ → Fin 3 → ℚ)
    (hcheck : planeCheckCanonicalTable bound values = true)
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (hb : q.beta 0 ≤ bound) : planeLowPsiValueWith values q = planeLowPsiValue q :=
  planeLowPsiValueWith_congr values planeCanonicalValues q hg hk
    (planeCheckCanonicalTable_sound bound values hcheck (q.beta 0) hb)

/-- Preserve the supplied ordered query through the existing occurrence adapter. -/
def planeLowPsiQueryKey (q : SurfaceQuery .plane) (hg : q.genus = 2) :
    SurfaceAncestorKey .plane :=
  SurfaceAncestorKey.ofLabels q.genus (Fin q.insertions.length)
    (by simp only [StableArity, hg]; omega) q.beta
    (fun i ↦ (q.insertions.get i).psi) (fun i ↦ (q.insertions.get i).label)

/-- The low-power query interface retains every state, exponent and occurrence. -/
def planeLowPsiQueryValue (q : SurfaceQuery .plane) (hg : q.genus = 2)
    (_hk : (∑ i : Fin q.insertions.length, (q.insertions.get i).psi) ≤ 1) : ℚ :=
  planeLowPsiValue (planeLowPsiQueryKey q hg)

section Interpretation
variable {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.plane.blowups)
    SurfaceTarget.plane.Curve SurfaceTarget.plane.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Modular scalar interpretation; the final geometry theorem supplies these
three values using the proved canonical reconstruction. -/
theorem planeLowPsiValueWith_eval (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (values : ℕ → Fin 3 → ℚ) (q : SurfaceAncestorKey .plane)
    (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (hv : ∀ j, values (q.beta 0) j = (planeCanonicalQueries (q.beta 0) j).eval U) :
    planeLowPsiValueWith values q =
      RationalTerms.eval (variableEval U P) (directNormalizedTerms q) := by
  apply RationalTerms.eval_congr
  intro t ht x hx
  obtain ⟨j, hj⟩ := normalizedTerms_plane_canonical_support q hg hk
    (show t ∈ normalizedTerms q by rwa [normalizedTerms_plane_eq_direct])
  rw [hj, Multiset.mem_singleton] at hx
  subst x
  rw [planeCanonicalValuation_apply]
  exact hv j

end Interpretation

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

/-- Every primary or first-power plane invariant is reconstructed from the
original geometric inputs and three finite seeds. Both interpretations are
proved; the ancestor equality uses the existing rational-tail comparison. -/
theorem planeLowPsiValue_from_geometry
    (q : SurfaceAncestorKey .plane) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1) :
    planeLowPsiValue q = q.descendantEval U ∧ planeLowPsiValue q = q.eval Omega P I := by
  have hc := planeCanonicalValues_from_geometry U P T laws H hpair Z F N J hWsource hboundary
    pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
    honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
    hglue hcotangent RT hout hHtwo (q.beta 0)
  have he := planeLowPsiValueWith_eval U P planeCanonicalValues q hg hk
    (fun j ↦ (congrFun hc j).symm)
  constructor
  · exact he.trans (eval_directNormalizedTerms_descendant U P T laws H hpair q (by omega) hk)
  · rw [← normalizedTerms_plane_eq_direct] at he
    exact he.trans (eval_normalizedTerms U P T laws H hpair Z F N J hWsource hboundary
      pW hpW hline (fun i ↦ Fin.elim0 i) hWoutput RT q)

/-- Full ordered queries with at most one descendant power have the actual
geometric checked value; neither state multiplicities nor labels are dropped. -/
theorem planeLowPsiQueryValue_checkedEval_from_geometry
    (q : SurfaceQuery .plane) (hg : q.genus = 2)
    (hk : (∑ i : Fin q.insertions.length, (q.insertions.get i).psi) ≤ 1) :
    q.checkedEval U = some (planeLowPsiQueryValue q hg hk) := by
  have hkey : (planeLowPsiQueryKey q hg).genus = 2 := hg
  have hpower : (planeLowPsiQueryKey q hg).totalPsi ≤ 1 := by
    simpa only [planeLowPsiQueryKey, SurfaceAncestorKey.totalPsi_ofLabels] using hk
  have hv := (planeLowPsiValue_from_geometry U P T laws H hpair Z F N J hWsource hboundary
    pW hpW hGsource GG hcycle pG hpG K hK pPsi hpPsi hpsi hfund hrows hloop hzeroTerms
    honeTerms hline hH hWoutput hGoutput HF pB hpB hlB hcB hinterior hsource
    hglue hcotangent RT hout hHtwo
    (planeLowPsiQueryKey q hg) hkey hpower).1
  have he : (planeLowPsiQueryKey q hg).descendantEval U = q.eval U :=
    SurfaceAncestorKey.descendantEval_ofLabels U _ _ _ _ _ _
  have hd : q.GeometricDomain := Or.inr (by simp only [StableArity, hg]; omega)
  rw [SurfaceQuery.checkedEval_of_geometricDomain U q hd]
  exact congrArg some (hv.trans he).symm

end Geometry

end AxiomaticGW.BelorousskiPandharipande
