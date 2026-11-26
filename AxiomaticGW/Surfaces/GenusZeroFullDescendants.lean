/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroDescendants
public import AxiomaticGW.Surfaces.DescendantStabilization
public import AxiomaticGW.Surfaces.DescendantKeys

/-!
# Genus-zero descendants at every finite arity

Sorted insertion occurrences give an executable stable evaluator on any finite
marking type. Multilinear basis expansion supplies the arbitrary states needed
by the existing anticanonical stabilization algorithm. Its callback is therefore
constructed from the same finite seeds, rather than supplied as extra data.
The query boundary rejects degree-zero unstable arities and nonzero genera.
-/

@[expose] public section

namespace AxiomaticGW

namespace SurfaceBasisLabel

/-- Expand every state in the existing finite surface basis. -/
theorem multilinear_eq_sum {X : SurfaceTarget} {S : Type} [Fintype S] [DecidableEq S]
    (f : MultilinearMap ℚ (fun _ : S ↦ SurfaceCohomology X.blowups) ℚ)
    (a : S → SurfaceCohomology X.blowups) :
    f a = ∑ b : S → SurfaceBasisLabel X,
      (∏ s, (b s).coordinate (a s)) * f (fun s ↦ (b s).value) := by
  have ha : a = fun s ↦ ∑ b : SurfaceBasisLabel X, b.coordinate (a s) • b.value := by
    funext s
    simpa only [labelBasis_apply, labelBasis_repr] using
      ((labelBasis X).sum_repr (a s)).symm
  conv_lhs => rw [ha]
  rw [f.map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [f.map_smul_univ, smul_eq_mul]

end SurfaceBasisLabel

namespace SurfaceGenusZero

/-- Stable basis values on arbitrary finite markings, using a computable sorted frame. -/
def stableBasisValue (X : SurfaceTarget) (S : Type) [Fintype S]
    (h : StableArity 0 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel X) : ℚ :=
  let q := SurfaceAncestorKey.ofLabels 0 S h beta k a
  stableValue X q.orderedInsertions.length (three_le_length q rfl)
    beta q.orderedPowers q.orderedLabels

/-- Multilinear expansion for the arbitrary states created by divisor reduction.
Zero coefficients are discarded before computing the corresponding basis value. -/
def stableStateValue (X : SurfaceTarget) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity 0 S) (beta : X.Curve) (k : S → ℕ)
    (a : S → SurfaceCohomology X.blowups) : ℚ :=
  ∑ b : S → SurfaceBasisLabel X, let w := ∏ s, (b s).coordinate (a s)
    if w = 0 then 0 else w * stableBasisValue X S h beta k b

/-- Total numerical evaluation, including the auxiliary zero-class unstable convention. -/
def value (X : SurfaceTarget) (beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S]
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) : ℚ :=
  SurfaceDescendant.stabilizedValue X 0 beta
    (fun S _ _ h k a ↦ stableStateValue X S h beta k a) S k a

/-- Geometric query evaluation; unsupported genera and auxiliary unstable zero
classes return `none`. Stable queries use the direct basis evaluator. -/
def queryValue? {X : SurfaceTarget} (q : SurfaceQuery X) : Option ℚ :=
  letI : Decidable (StableArity q.genus (Fin q.insertions.length)) :=
    inferInstanceAs (Decidable (2 < 2 * q.genus + Fintype.card (Fin q.insertions.length)))
  if hg : q.genus = 0 then
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
  (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
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
  (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
  (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
  (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible Z F N)
  {G : StableMapIntersection U} {St : StableMapStabilization G}
  (Tail : RationalTailIntersection G St P)

include P T laws H hpair Z F N J hsource hboundary p hp K hK hterms hline hE houtput Tail

theorem stableBasisValue_eq (S : Type) [Fintype S] (h : StableArity 0 S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceBasisLabel X) :
    stableBasisValue X S h beta k a = U.invariant 0 S beta k (fun s ↦ (a s).value) := by
  rw [stableBasisValue, stableValue_eq U P T laws H hpair Z F N J hsource hboundary p hp
    K hK hterms hline hE houtput Tail]
  exact (SurfaceAncestorKey.descendantEval_eq_ordered U
    (SurfaceAncestorKey.ofLabels 0 S h beta k a)).symm.trans
      (SurfaceAncestorKey.descendantEval_ofLabels U 0 S h beta k a)

theorem stableStateValue_eq (S : Type) [Fintype S] [DecidableEq S] (h : StableArity 0 S)
    (beta : X.Curve) (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    stableStateValue X S h beta k a = U.invariant 0 S beta k a := by
  rw [stableStateValue, ← U.invariantMap_apply 0 S beta k a,
    SurfaceBasisLabel.multilinear_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  split_ifs with hw
  · rw [hw, zero_mul]
  · rw [stableBasisValue_eq U P T laws H hpair Z F N J hsource hboundary p hp K hK hterms
      hline hE houtput Tail, U.invariantMap_apply]

/-- The existing proved stabilization bound now reconstructs every genus-zero
descendant from the same finite seeds, without a stable-value callback. -/
theorem value_eq (beta : X.Curve) (S : Type) [Fintype S] [DecidableEq S]
    (k : S → ℕ) (a : S → SurfaceCohomology X.blowups) :
    value X beta S k a = U.invariant 0 S beta k a := by
  apply SurfaceDescendant.stabilizedValue_eq_invariant U T laws H hpair
  intro S _ _ h k a
  rw [stableStateValue_eq U P T laws H hpair Z F N J hsource hboundary p hp K hK hterms
    hline hE houtput Tail, U.invariant_of_stable 0 S h]

/-- Every genus-zero query is answered exactly on the original geometric domain. -/
theorem queryValue?_eq_checkedEval (q : SurfaceQuery X) (hg : q.genus = 0) :
    queryValue? q = q.checkedEval U := by
  rw [queryValue?, dif_pos hg]
  by_cases h : StableArity q.genus (Fin q.insertions.length)
  · rw [dif_pos h, stableQueryValue_eq U P T laws H hpair Z F N J hsource hboundary p hp
      K hK hterms hline hE houtput Tail, SurfaceQuery.checkedEval,
      if_pos (show q.GeometricDomain from Or.inr h)]
  · rw [dif_neg h, SurfaceQuery.checkedEval]
    by_cases hb : q.beta = 0
    · rw [if_pos hb, if_neg]
      exact fun hd ↦ hd.elim (fun hn ↦ hn hb) h
    · rw [if_neg hb, if_pos (show q.GeometricDomain from Or.inl hb),
        value_eq U P T laws H hpair Z F N J hsource
        hboundary p hp K hK hterms hline hE houtput Tail, SurfaceQuery.eval, hg]

end SurfaceGenusZero
end AxiomaticGW
