/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoMarkedPairLookup

/-! # Genus-two divisor pairs for which both singleton coefficients vanish

No singleton value is needed. The ordered recognition has the same priority as the public
marked evaluator, including its handling of units. Geometric soundness uses the divisor and
string/dilaton laws and the surface cup and curve pairing, independently of reconstruction seeds.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceGenusTwoBlowupDescendants (CheckedDescendant)
variable {X : SurfaceTarget}

/-- Run the established marked-pair equations with the empty singleton table. -/
def zeroDivisorPair? (q : SurfaceQuery X) : Option ℚ :=
  markedPairValueWith? (fun _ ↦ none) q

/-- Recognition at arbitrary ordered inputs demands a genuine primary divisor and vanishing
of both its full curve intersection and the survivor's signed lowered-cotangent coefficient. -/
theorem zeroDivisorPair?_iff (q : SurfaceQuery X) (v : ℚ) :
    zeroDivisorPair? q = some v ↔ v = 0 ∧ unitPairReduction? q = none ∧
      ∃ d s, divisorPairReduction? q = some (d, s) ∧ d.primaryFactor q.beta = 0 ∧
        cupCoefficient d s = 0 := by
  cases hu : unitPairReduction? q with
  | some p =>
    rcases p with ⟨rule, s⟩
    simp only [zeroDivisorPair?, markedPairValueWith?, hu, Option.map_none, reduceCtorEq, false_and,
      and_false]
  | none =>
    cases hd : divisorPairReduction? q with
    | none =>
      simp [zeroDivisorPair?, markedPairValueWith?, divisorPairValueWith?, hu, hd]
    | some p =>
      rcases p with ⟨d, s⟩
      by_cases h₁ : d.primaryFactor q.beta = 0 <;> by_cases h₂ : cupCoefficient d s = 0 <;>
        simp [zeroDivisorPair?, markedPairValueWith?, divisorPairValueWith?, weightedSingleton?,
          hu, hd, h₁, h₂, eq_comm (a := v)]

/-- The finite computation supplies the existing ordered arithmetic descendant witness. -/
theorem zeroDivisorPair?_checked (i : Fin X.blowups) (q : SurfaceQuery X) {v : ℚ}
    (h : zeroDivisorPair? q = some v) : CheckedDescendant i q v :=
  markedPairValueWith?_checked i (by simp) h

/-- At any recognized pair, the original two-term divisor evaluator returns the same value
at every exceptional pivot. -/
theorem zeroDivisorPair?_original (i : Fin X.blowups) (q : SurfaceQuery X) {v : ℚ}
    (h : zeroDivisorPair? q = some v) : divisorPairValue? i q = some v := by
  obtain ⟨rfl, _, d, s, hd, h₁, h₂⟩ := (zeroDivisorPair?_iff q v).mp h
  simp [divisorPairValue?, divisorPairValueWith?, hd, weightedSingleton?, h₁, h₂]

/-- The actual checked geometric descendant vanishes by the divisor equation. No singleton
evaluation, WDVV, higher-genus relation, or numerical seed enters the statement. -/
theorem zeroDivisorPair?_checkedEval {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F} {L : DescendantDivisorLaw M I A}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I) (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (q : SurfaceQuery X) {v : ℚ}
    (h : zeroDivisorPair? q = some v) : q.checkedEval U = some v := by
  obtain ⟨rfl, _, d, s, hd, h₁, h₂⟩ := (zeroDivisorPair?_iff q v).mp h
  obtain ⟨hc, last, hq⟩ := divisorPairReduction?_sound q hd
  rw [SurfaceQuery.checkedEval_of_geometricDomain U q (Or.inr (by
    have hg : q.genus = 2 := congrArg SurfaceQuery.genus hq
    simp only [StableArity, hg]
    omega))]
  apply congrArg some
  calc q.eval U = (divisorPair last q.beta d s).eval U := congrArg (SurfaceQuery.eval U) hq
    _ = _ := (eval_divisorPair U T laws H hpair last q.beta d hc s).trans (by
        rw [h₁, h₂, zero_mul, zero_mul, zero_add])

end AxiomaticGW.SurfaceGenusTwo
