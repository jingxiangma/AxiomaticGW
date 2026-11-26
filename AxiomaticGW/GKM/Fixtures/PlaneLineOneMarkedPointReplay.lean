/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneLineOneMarkedPoint
public import AxiomaticGW.Surfaces.GenusZeroFullDescendants

/-! # Geometric interpretation of the ordinary specialization for a marked plane line -/

@[expose] public section
namespace AxiomaticGW.GKM.PlaneLineOneMarkedPoint
open EquivariantCoefficients

/-- The ordinary dimension equation selects precisely the first cotangent power. -/
theorem dimension_iff (k : ℕ) : (requests k).DimensionCompatible ↔ k = 1 := by
  have hw : (requests k).totalCodimension = 2 + k := by
    change (∑ j : Fin 1, (((requests k).insertions.get j).label.codimension +
      ((requests k).insertions.get j).psi)) = 2 + k
    rw [Fin.sum_univ_one]
    rfl
  unfold SurfaceQuery.DimensionCompatible
  rw [hw]
  change ((2 + k : ℕ) : ℤ) = 3 + 0 - 1 + 1 ↔ k = 1
  omega

/-- The dimension-matched value comes from the original positive-degree genus-zero recursion. -/
theorem first_descendant : SurfaceGenusZero.queryValue? (requests 1) = some 1 := by
  decide +kernel

/-- The computed ordinary geometric evaluation and the two-flag specialization agree for
every power. Only the original plane line seed enters the genus-zero reconstruction. -/
theorem geometric_comparison {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology 0) SurfaceTarget.plane.Curve
      SurfaceTarget.plane.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (P : PsiClasses C)
    (T : SurfaceTheoryIdentification .plane Omega) (laws : DescendantStringDilatonLaws M I)
    {Fdiv : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega Fdiv}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility F N)
    (hsource : ∀ i, (WDVV.expression i).Compatible Z F N)
    (hboundary : WDVV.BoundaryClassesEqual F)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (K : PsiForgetFormula P) (hK : PsiBoundaryExpansion.TailCompatible K F N)
    (hterms : ∀ n t, t ∈ PsiBoundaryExpansion.genusZeroTerms 0 n → t.2.Compatible Z F N)
    (hline : (SurfaceSeed.line : SurfaceSeed .plane).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (Tail : RationalTailIntersection G St P) (k : ℕ) {v : ℚ} (hv : Specializes (equivariant k) v) :
    (requests k).checkedEval U = some v := by
  rw [Specializes.unique hv (specializes k)]
  by_cases hk : k = 1
  · subst k
    simp only [if_true]
    rw [← SurfaceGenusZero.queryValue?_eq_checkedEval U P T laws H hpair Z F N J hsource
      hboundary p hp K hK hterms hline (fun j ↦ j.elim0) houtput Tail (requests 1) rfl]
    exact first_descendant
  · have hg : (requests k).GeometricDomain := Or.inl
      (by decide +kernel : (![1] : SurfaceTarget.plane.Curve) ≠ 0)
    have hd := mt (dimension_iff k).mp hk
    rw [if_neg hk, SurfaceQuery.checkedEval_of_geometricDomain U _ hg,
      SurfaceQuery.eval_eq_zero_of_dimension_incompatible U T _ hd]

end AxiomaticGW.GKM.PlaneLineOneMarkedPoint
