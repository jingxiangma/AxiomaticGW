/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusZeroReconstruction
public import AxiomaticGW.Surfaces.GenusZeroScalar

/-!
# Finite certificates for reconstructed genus-zero point values

A candidate supplies exact values. The checker verifies every original initial
value or proved scalar WDVV equation in the requested energy bound. Strict
decrease and complete bounded enumeration then identify the whole candidate
with the existing well-founded reconstruction. No recursive computation of
lower tables is required during certificate replay.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusZero

/-- The exact equation to check at a class, with lower values supplied as candidate data. -/
def checkValue (X : SurfaceTarget) (v : X.Curve → ℚ) (beta : X.Curve) : Bool :=
  decide (v beta = if IsInitial X beta then initialValue X beta else
    scalarReconstructionStep X beta v)

/-- Every full class in the held bound must pass, including all zero-valued classes. -/
def checkBoundedValues (X : SurfaceTarget) (bound : ℕ) (v : X.Curve → ℚ) : Bool :=
  decide (∀ beta ∈ X.bounded bound, checkValue X v beta = true)

/-- Candidate literal tuples can replace generated function representations only
after their finite set is checked against the complete original bounded set. -/
def checkEnumeratedValues (X : SurfaceTarget) (bound : ℕ) (classes : List X.Curve)
    (v : X.Curve → ℚ) : Bool :=
  decide (classes.toFinset = X.bounded bound) && classes.all (checkValue X v)

/-- Explicit tuple enumeration discharges precisely the original bounded checker.
Dropping a zero-valued class still fails the coverage equality. -/
theorem checkEnumeratedValues_sound (X : SurfaceTarget) (bound : ℕ)
    (classes : List X.Curve) (v : X.Curve → ℚ)
    (hcheck : checkEnumeratedValues X bound classes v = true) :
    checkBoundedValues X bound v = true := by
  rw [checkEnumeratedValues, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcheck
  rw [checkBoundedValues, decide_eq_true_eq]
  intro beta hb
  apply hcheck.2 beta
  rw [← List.mem_toFinset, hcheck.1]
  exact hb

/-- Accepted finite equations determine all values in the bound. The candidate
is untrusted data: the entire hypothesis is an executable finite equality check. -/
theorem checkBoundedValues_sound (X : SurfaceTarget) (bound : ℕ) (v : X.Curve → ℚ)
    (hcheck : checkBoundedValues X bound v = true)
    (beta : X.Curve) (hbound : X.effective.energy beta ≤ bound) :
    v beta = pointValue X beta := by
  have hrows : ∀ b ∈ X.bounded bound, v b =
      if IsInitial X b then initialValue X b else
        compactReconstructionStep X b (fun u ↦ v (variableCurve u)) := by
    simpa only [checkBoundedValues, decide_eq_true_eq, checkValue, scalarReconstructionStep_eq]
      using hcheck
  induction beta using (measure (fun b : X.Curve ↦ X.effective.energy b)).wf.induction with
  | h beta ih =>
    have hb : beta ∈ X.bounded bound := by
      rw [SurfaceTarget.bounded_eq, X.effective.mem_bounded]
      exact hbound
    rw [hrows beta hb]
    by_cases hinit : IsInitial X beta
    · rw [if_pos hinit, pointValue_initial X beta hinit]
    · rw [if_neg hinit, compactReconstructionStep_eq X beta hinit, pointValue_step X beta hinit]
      congr 2
      apply RationalTerms.eval_congr
      intro t ht u hu
      obtain ⟨gamma, _, rfl, hlt⟩ := reconstructionRemainder_dependencies X beta t ht u hu
      exact ih gamma hlt (by omega)

/-- Bind a numerical certificate to a positive class, claimed value and energy bound.
Degree-zero empty point requests are auxiliary conventions and are rejected here. -/
def checkPointClaim (X : SurfaceTarget) (bound : ℕ) (v : X.Curve → ℚ)
    (beta : X.Curve) (claimed : ℚ) : Bool :=
  decide (beta ≠ 0 ∧ X.effective.energy beta ≤ bound ∧ v beta = claimed) &&
    checkBoundedValues X bound v

/-- A held point claim is proved by the original terminating evaluator. -/
theorem checkPointClaim_sound (X : SurfaceTarget) (bound : ℕ) (v : X.Curve → ℚ)
    (beta : X.Curve) (claimed : ℚ)
    (hcheck : checkPointClaim X bound v beta claimed = true) :
    beta ≠ 0 ∧ pointValue X beta = claimed := by
  rw [checkPointClaim, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1,
    (checkBoundedValues_sound X bound v hcheck.2 beta hcheck.1.2.1).symm.trans hcheck.1.2.2⟩

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (I : StableCurveIntegration C)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hsource : ∀ i, (WDVV.expression i).Compatible A F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (p : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hp : WDVV.AcceptsExchange p)
  (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)

include A F N H hsource hboundary p hp P T S Hdiv hpair

/-- A finite accepted table has the same geometric interpretation as the original evaluator. -/
theorem checkBoundedValues_eq_eval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (bound : ℕ) (v : X.Curve → ℚ) (hcheck : checkBoundedValues X bound v = true)
    (beta : X.Curve) (hbound : X.effective.energy beta ≤ bound) :
    v beta = (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).eval U :=
  (checkBoundedValues_sound X bound v hcheck beta hbound).trans
    (pointValue_eq_eval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
      hline hE houtput beta)

/-- An accepted held claim is a geometric checked query, never a degree-zero auxiliary value. -/
theorem checkPointClaim_checkedEval
    (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
    (hE : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
    (houtput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (bound : ℕ) (v : X.Curve → ℚ) (beta : X.Curve) (claimed : ℚ)
    (hcheck : checkPointClaim X bound v beta claimed = true) :
    (SurfaceQuery.points X 0 beta (X.effective.energy beta - 1)).checkedEval U =
      some claimed := by
  obtain ⟨hbeta, hvalue⟩ := checkPointClaim_sound X bound v beta claimed hcheck
  rw [SurfaceQuery.checkedEval_of_geometricDomain U _ (Or.inl hbeta)]
  rw [← pointValue_eq_eval A I F N H hsource hboundary p hp Omega P T U S Hdiv hpair
    hline hE houtput beta, hvalue]

end AxiomaticGW.SurfaceGenusZero
