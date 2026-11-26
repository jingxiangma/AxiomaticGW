/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneReconstruction
public import AxiomaticGW.Surfaces.GenusOneSymmetry
public import AxiomaticGW.Surfaces.GenusZeroCertificate

/-!
# Finite certificates for reconstructed genus-one point values

The joint checker accepts both rational and elliptic candidate tables only
after checking their defining equations throughout the same complete energy
bound. Rational dependencies can have the original energy; elliptic
dependencies strictly decrease. Thus a certified rational table can be
reused without treating its unverified numerical contents as an oracle.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

open SurfaceLowGenus
open SurfaceGenusZero (variableCurve)

/-- The original initial value or scalar Getzler equation at a full curve class. -/
def checkValue (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) (beta : X.Curve) : Bool :=
  decide (v₁ beta = if IsInitial X beta then 0 else orbitReconstructionStep X beta v₀ v₁)

/-- Check both genera throughout the held bound, including zero-valued classes. -/
def checkBoundedValues (X : SurfaceTarget) (bound : ℕ) (v₀ v₁ : X.Curve → ℚ) : Bool :=
  SurfaceGenusZero.checkBoundedValues X bound v₀ &&
    decide (∀ beta ∈ X.bounded bound, checkValue X v₀ v₁ beta = true)

/-- Literal class tuples may replace generated representations after exact coverage is checked. -/
def checkEnumeratedValues (X : SurfaceTarget) (bound : ℕ) (classes : List X.Curve)
    (v₀ v₁ : X.Curve → ℚ) : Bool :=
  SurfaceGenusZero.checkBoundedValues X bound v₀ &&
    (decide (classes.toFinset = X.bounded bound) && classes.all (checkValue X v₀ v₁))

/-- Enumerated replay discharges the complete checker without dropping vanishing rows. -/
theorem checkEnumeratedValues_sound (X : SurfaceTarget) (bound : ℕ)
    (classes : List X.Curve) (v₀ v₁ : X.Curve → ℚ)
    (hcheck : checkEnumeratedValues X bound classes v₀ v₁ = true) :
    checkBoundedValues X bound v₀ v₁ = true := by
  rw [checkEnumeratedValues, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true] at hcheck
  rw [checkBoundedValues, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hcheck.1, ?_⟩
  intro beta hb
  apply hcheck.2.2 beta
  rw [← List.mem_toFinset, hcheck.2.1]
  exact hb

/-- Accepted finite equations determine the elliptic values in the requested bound.
The rational component is checked by the existing independent genus-zero checker. -/
theorem checkBoundedValues_sound (X : SurfaceTarget) (bound : ℕ) (v₀ v₁ : X.Curve → ℚ)
    (hcheck : checkBoundedValues X bound v₀ v₁ = true)
    (beta : X.Curve) (hbound : X.effective.energy beta ≤ bound) :
    v₁ beta = pointValue X beta := by
  rw [checkBoundedValues, Bool.and_eq_true] at hcheck
  have hzero := SurfaceGenusZero.checkBoundedValues_sound X bound v₀ hcheck.1
  have hrows : ∀ b ∈ X.bounded bound, v₁ b = if IsInitial X b then 0 else
      compactReconstructionStep X b (pointValuation v₀ v₁) := by
    simpa only [decide_eq_true_eq, checkValue, orbitReconstructionStep_eq,
      scalarReconstructionStep_eq] using hcheck.2
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
      have hle := reconstructionRemainder_energy_le X beta t ht u hu
      obtain ⟨g, gamma, _, rfl, _, hlt⟩ := reconstructionRemainder_dependencies X beta t ht u hu
      simp only [pointValuation_point]
      by_cases hg : g = 0
      · simp only [if_pos hg]
        exact hzero gamma (hle.trans hbound)
      · simp only [if_neg hg]
        exact ih gamma (hlt.resolve_left hg) (hle.trans hbound)

/-- Bind a numerical certificate to a positive full class, claimed value and energy bound.
The degree-zero empty point value is auxiliary and cannot be accepted as a geometric claim. -/
def checkPointClaim (X : SurfaceTarget) (bound : ℕ) (v₀ v₁ : X.Curve → ℚ)
    (beta : X.Curve) (claimed : ℚ) : Bool :=
  decide (beta ≠ 0 ∧ X.effective.energy beta ≤ bound ∧ v₁ beta = claimed) &&
    checkBoundedValues X bound v₀ v₁

/-- An accepted held point claim is proved by the original terminating evaluator. -/
theorem checkPointClaim_sound (X : SurfaceTarget) (bound : ℕ) (v₀ v₁ : X.Curve → ℚ)
    (beta : X.Curve) (claimed : ℚ)
    (hcheck : checkPointClaim X bound v₀ v₁ beta claimed = true) :
    beta ≠ 0 ∧ pointValue X beta = claimed := by
  rw [checkPointClaim, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1,
    (checkBoundedValues_sound X bound v₀ v₁ hcheck.2 beta hcheck.1.2.1).symm.trans hcheck.1.2.2⟩

variable {X : SurfaceTarget} {C : StableCurveCohomology ℚ}
  (A : ∀ g S, [Fintype S] → StrataRealization C g S)
  (I : StableCurveIntegration C)
  (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I)
  (H : GluingForgetfulCompatibility F N)
  (hWsource : ∀ i, (WDVV.expression i).Compatible A F N)
  (hboundary : WDVV.BoundaryClassesEqual F)
  (pW : RelationCertificate.Presentation 0 (Fin 4) 2 3) (hpW : WDVV.AcceptsExchange pW)
  (hGsource : ∀ i, (GetzlerGraphs.expression i).Compatible A F N)
  (G : GetzlerRelationGeometry C)
  (hcycle : ∀ x, (A 1 (Fin 4)).map (GetzlerGraphs.cycle x) = G.cycle x)
  (pG : RelationCertificate.Presentation 1 (Fin 4) 1 33)
  (hpG : GetzlerGraphs.AcceptsExchange pG)
  (Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C)
  (P : PsiClasses C) (T : SurfaceTheoryIdentification X Omega)
  {M : StableMapDescendants Omega} (U : UnstableDescendantConventions M I)
  (S : DescendantStringDilatonLaws M I)
  {Fdiv : ForgetfulPushforward C I} {Adiv : GWDivisorAxiom Omega Fdiv}
  {L : DescendantDivisorLaw M I Adiv} (Hdiv : FullDescendantDivisorLaw U L)
  (hpair : T.DivisorPairingCompatible Adiv)
  (hline : (SurfaceSeed.line : SurfaceSeed X).query.eval U = 1)
  (hEzero : ∀ i, (SurfaceSeed.exceptional i : SurfaceSeed X).query.eval U = 1)
  (hH : (SurfaceSeed.genusOneHyperplane : SurfaceSeed X).query.eval U = -1 / 8)
  (hE : ∀ i, (SurfaceSeed.genusOneExceptional i : SurfaceSeed X).query.eval U = -1 / 24)

include A F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG P T S Hdiv hpair
  hline hEzero hH hE

/-- A finite accepted joint table has the original geometric interpretation. -/
theorem checkBoundedValues_eq_eval
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (bound : ℕ) (v₀ v₁ : X.Curve → ℚ)
    (hcheck : checkBoundedValues X bound v₀ v₁ = true)
    (beta : X.Curve) (hbound : X.effective.energy beta ≤ bound) :
    v₁ beta = (SurfaceQuery.points X 1 beta (X.effective.energy beta)).eval U :=
  (checkBoundedValues_sound X bound v₀ v₁ hcheck beta hbound).trans
    (pointValue_eq_eval A I F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG
      Omega P T U S Hdiv hpair hline hEzero hH hE hWoutput hGoutput beta)

/-- An accepted held claim is a checked geometric query under the named original inputs. -/
theorem checkPointClaim_checkedEval
    (hWoutput : ∀ n i z, z ∈ (WDVV.expression i).addMarkings n → z.Compatible A F N)
    (hGoutput : ∀ n i z, z ∈ (GetzlerGraphs.expression i).addMarkings n → z.Compatible A F N)
    (bound : ℕ) (v₀ v₁ : X.Curve → ℚ) (beta : X.Curve) (claimed : ℚ)
    (hcheck : checkPointClaim X bound v₀ v₁ beta claimed = true) :
    (SurfaceQuery.points X 1 beta (X.effective.energy beta)).checkedEval U = some claimed := by
  obtain ⟨hbeta, hvalue⟩ := checkPointClaim_sound X bound v₀ v₁ beta claimed hcheck
  rw [SurfaceQuery.checkedEval_of_geometricDomain U _ (Or.inl hbeta)]
  rw [← pointValue_eq_eval A I F N H hWsource hboundary pW hpW hGsource G hcycle pG hpG
    Omega P T U S Hdiv hpair hline hEzero hH hE hWoutput hGoutput beta, hvalue]

end AxiomaticGW.SurfaceGenusOne
