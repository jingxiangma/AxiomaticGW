/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.MixedAncestorReduction

/-!
# Complete three-marked genus-zero descendant reconstruction

On the zero-dimensional stable-curve space with three rational markings,
every positive ancestor power vanishes. The mixed reduction therefore closes
against the already reconstructed primary sector. This gives a total exact
algorithm for arbitrary three-point descendant powers and full effective
classes on all three fixed surfaces, with no invariant-value callback.

This sector does not assert reconstruction at larger marking count or genus.
Geometric soundness retains the explicit virtual comparison inputs and the
original finite-seed WDVV contract.
-/

@[expose] public section

namespace AxiomaticGW
namespace SurfaceDescendant

/-- Terminal valuation for the three-marked rational sector only. Its use
outside this sector has no invariant interpretation. -/
def threePointAncestorValue {X : SurfaceTarget} (q : SurfaceAncestorKey X) : ℚ :=
  if q.IsPrimary then SurfaceGenusZero.primaryValue X q.beta q.primaryLabels else 0

/-- Exact reconstruction of three-marked rational descendants at every class
and every cotangent power, including the degree-zero sector. -/
def threePointValue (X : SurfaceTarget) (beta : X.Curve) (d : Fin 3 → ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  RationalTerms.eval threePointAncestorValue
    (mixedAncestorTerms 0 (Fin 3) StableArity.zero_fin_three (List.finRange 3) beta d 0 a)

section Soundness
variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
  {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
  (U : UnstableDescendantConventions M I) (P : PsiClasses C)

/-- Primary reconstruction suffices for every terminal variable produced by
the three-point reduction; nonprimary ancestors vanish on the curve space. -/
theorem threePointAncestorValue_eq_ofLabels
    (hprimary : ∀ beta m, SurfaceGenusZero.primaryValue X beta m =
      SurfacePrimary.eval U 0 beta m)
    (beta : X.Curve) (e : Fin 3 → ℕ) (a : Fin 3 → SurfaceBasisLabel X) :
    threePointAncestorValue
        (SurfaceAncestorKey.ofLabels 0 (Fin 3) StableArity.zero_fin_three beta e a) =
      (SurfaceAncestorKey.ofLabels 0 (Fin 3) StableArity.zero_fin_three beta e a).eval
        Omega P I := by
  let q := SurfaceAncestorKey.ofLabels 0 (Fin 3) StableArity.zero_fin_three beta e a
  change threePointAncestorValue q = q.eval Omega P I
  by_cases hp : q.IsPrimary
  · rw [threePointAncestorValue, if_pos hp, q.eval_eq_primary U P hp, hprimary]
    rfl
  · rw [threePointAncestorValue, if_neg hp]
    have he : ∃ s, e s ≠ 0 := by
      by_contra hn
      apply hp
      intro b hb
      change b ∈ (Finset.univ : Finset (Fin 3)).val.map (fun s ↦ ⟨a s, e s⟩) at hb
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.mp hb
      exact not_exists_not.mp hn s
    obtain ⟨s, hs⟩ := he
    have hpsi : P.psi 0 (Fin 3) StableArity.zero_fin_three s = 0 := by
      apply C.eq_zero_of_dimension_lt 0 (Fin 3) StableArity.zero_fin_three 1 _
        (P.psi_degree _ _ _ _)
      norm_num [StableArity.dimension]
    have hmon : P.monomial 0 (Fin 3) StableArity.zero_fin_three e = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      rw [hpsi, zero_pow hs]
    rw [SurfaceAncestorKey.eval_ofLabels]
    change 0 = Omega.ancestorInvariant P I 0 (Fin 3) StableArity.zero_fin_three
      beta e (fun s ↦ (a s).value)
    rw [GromovWittenTheory.ancestorInvariant_apply, hmon, mul_zero, map_zero]

/-- Intermediate composition theorem: both identifications are discharged by
the finite-seed reconstruction theorem below, not assumed as numerical data. -/
theorem threePointValue_eq_of_identifications
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (K : RationalTailIntersection G St P)
    (hcal : ∀ power beta row col, reconstructedCalibrationMatrix X power beta row col =
      row.coordinate (U.calibrationCoefficient power beta col.value))
    (hprimary : ∀ beta m, SurfaceGenusZero.primaryValue X beta m =
      SurfacePrimary.eval U 0 beta m)
    (beta : X.Curve) (d : Fin 3 → ℕ) (a : Fin 3 → SurfaceBasisLabel X) :
    threePointValue X beta d a = U.invariant 0 (Fin 3) beta d (fun s ↦ (a s).value) := by
  rw [threePointValue, eval_mixedAncestorTerms_congr threePointAncestorValue
    (SurfaceAncestorKey.eval Omega P I) 0 (Fin 3) StableArity.zero_fin_three
      (threePointAncestorValue_eq_ofLabels U P hprimary)]
  rw [eval_mixedAncestorTerms K hcal, M.mixedInvariant_zero_ancestor,
    U.invariant_of_stable 0 (Fin 3) StableArity.zero_fin_three]
  intro s hs
  exact False.elim (hs (List.mem_finRange s))

/-- Every three-marked rational descendant is reconstructed from the original
WDVV inputs and finite line/exceptional seeds, at arbitrary power and class. -/
theorem threePointValue_eq
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F}
    {L : DescendantDivisorLaw M I A} (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A)
    (Z : ∀ g S, [Fintype S] → StrataRealization C g S)
    (Fsep : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
    (J : GluingForgetfulCompatibility Fsep N)
    (hsource : ∀ i, (WDVV.expression i).Compatible Z Fsep N)
    (hboundary : WDVV.BoundaryClassesEqual Fsep)
    (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z Fsep N)
    {G : StableMapIntersection U} {St : StableMapStabilization G}
    (K : RationalTailIntersection G St P)
    (beta : X.Curve) (d : Fin 3 → ℕ) (a : Fin 3 → SurfaceBasisLabel X) :
    threePointValue X beta d a = U.invariant 0 (Fin 3) beta d (fun s ↦ (a s).value) :=
  threePointValue_eq_of_identifications U P K
    (reconstructedCalibrationMatrix_eq U T laws H hpair Z Fsep N J hsource hboundary
      p hp P hline hE houtput K)
    (SurfaceGenusZero.primaryValue_eq_eval Z I Fsep N J hsource hboundary p hp Omega P
      T U laws H hpair hline hE houtput) beta d a

end Soundness
end SurfaceDescendant
end AxiomaticGW
