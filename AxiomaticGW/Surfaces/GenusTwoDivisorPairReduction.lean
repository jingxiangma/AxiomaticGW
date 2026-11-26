/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoDivisorPairs

/-! # Two calibrated singleton contributions of an ordered primary divisor pair -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceGenusTwoBlowupDescendants SurfaceDescendant
variable {X : SurfaceTarget}

/-- Recognize a primary divisor in either slot, keeping the unmodified surviving insertion. -/
def divisorPairReduction? (q : SurfaceQuery X) :
    Option (SurfaceBasisLabel X × SurfaceInsertion X) :=
  match q with
  | ⟨2, _, [s, t]⟩ =>
    if s.psi = 0 ∧ s.label.codimension = 1 then some (s.label, t) else
    if t.psi = 0 ∧ t.label.codimension = 1 then some (t.label, s) else none
  | _ => none

/-- Recognition preserves the full ordered query and only selects actual divisors. -/
theorem divisorPairReduction?_sound (q : SurfaceQuery X) {d : SurfaceBasisLabel X}
    {s : SurfaceInsertion X} (h : divisorPairReduction? q = some (d, s)) :
    d.codimension = 1 ∧ ∃ last, q = divisorPair last q.beta d s := by
  unfold divisorPairReduction? at h
  split at h
  · rename_i beta a b
    rcases a with ⟨a, p⟩
    rcases b with ⟨b, k⟩
    split_ifs at h with ha hb
    · obtain ⟨rfl, rfl⟩ := Option.some.inj h
      obtain ⟨rfl, ha⟩ := ha
      exact ⟨ha, false, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Option.some.inj h
      obtain ⟨rfl, hb⟩ := hb
      exact ⟨hb, true, rfl⟩
  · contradiction

/-- A vanishing scalar term needs no singleton lookup. -/
def weightedSingleton? (one : SurfaceQuery X → Option ℚ) (c : ℚ)
    (beta : X.Curve) (s : SurfaceInsertion X) : Option ℚ :=
  if c = 0 then some 0 else (one ⟨2, beta, [s]⟩).map (c * ·)

theorem weightedSingleton?_eq (one : SurfaceQuery X → Option ℚ) (c : ℚ) (beta : X.Curve)
    (s : SurfaceInsertion X) (v : ℚ) (h : c ≠ 0 → one ⟨2, beta, [s]⟩ = some v) :
    weightedSingleton? one c beta s = some (c * v) := by
  unfold weightedSingleton?
  split_ifs with hc
  · rw [hc, zero_mul]
  · rw [h hc]; rfl

/-- Evaluate the curve-intersection term and the lowered signed cup term separately. -/
def divisorPairValueWith? (one : SurfaceQuery X → Option ℚ) (q : SurfaceQuery X) : Option ℚ :=
  match divisorPairReduction? q with
  | none => none
  | some (d, s) =>
    (weightedSingleton? one (d.primaryFactor q.beta) q.beta s).bind fun main ↦
      (weightedSingleton? one (cupCoefficient d s) q.beta (cupInsertion d s)).map (main + ·)

/-- Every accepted singleton substitution enters with the original two coefficients. -/
theorem divisorPairValueWith?_of_singletons (one : SurfaceQuery X → Option ℚ) (q : SurfaceQuery X)
    (d : SurfaceBasisLabel X) (s : SurfaceInsertion X) (a b : ℚ)
    (h : divisorPairReduction? q = some (d, s))
    (ha : d.primaryFactor q.beta ≠ 0 → one ⟨2, q.beta, [s]⟩ = some a)
    (hb : cupCoefficient d s ≠ 0 → one ⟨2, q.beta, [cupInsertion d s]⟩ = some b) :
    divisorPairValueWith? one q = some (d.primaryFactor q.beta * a + cupCoefficient d s * b) := by
  simp only [divisorPairValueWith?, h, weightedSingleton?_eq _ _ _ _ a ha,
    weightedSingleton?_eq _ _ _ _ b hb]
  rfl

/-- Apply the two-term formula to the original finite blowup singleton evaluator. -/
def divisorPairValue? (i : Fin X.blowups) (q : SurfaceQuery X) : Option ℚ :=
  divisorPairValueWith? (queryValue? i) q

/-- Each of the two singleton terms keeps its complete mixed ancestor and positive-tail
calibration polynomial, including lower powers at the same full effective class. -/
theorem divisorPairValueWith?_calibrated (v : SurfaceGenusTwoBlowupOrder.State X → ℚ)
    (q : SurfaceQuery X) (d : SurfaceBasisLabel X) (s : SurfaceInsertion X)
    (h : divisorPairReduction? q = some (d, s)) :
    let cal (t : SurfaceInsertion X) :=
      RationalTerms.eval (ancestorValueWith v)
        (oneMarkingTerms (reconstructedCalibrationMatrix X) q.beta t.label t.psi 0)
    divisorPairValueWith? (queryValueWith? v) q =
      some (d.primaryFactor q.beta * cal s + cupCoefficient d s * cal (cupInsertion d s)) := by
  apply divisorPairValueWith?_of_singletons _ _ _ _ _ _ h
  · intro _; exact queryValueWith?_oneMarking v _ _ _
  · intro _; exact queryValueWith?_oneMarking v _ _ _

/-- Given identification of the original singleton evaluators, the finite divisor sum
computes the actual ordered geometric descendant. -/
theorem divisorPair_checkedEval_of_identification {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F} {L : DescendantDivisorLaw M I A}
    (U : UnstableDescendantConventions M I) (T : SurfaceTheoryIdentification X Omega)
    (laws : DescendantStringDilatonLaws M I) (H : FullDescendantDivisorLaw U L)
    (hpair : T.DivisorPairingCompatible A) (one : SurfaceQuery X → Option ℚ)
    (hid : ∀ (beta : X.Curve) (s : SurfaceInsertion X),
      one ⟨2, beta, [s]⟩ = some (SurfaceQuery.eval U ⟨2, beta, [s]⟩))
    (q : SurfaceQuery X) {v : ℚ} (hv : divisorPairValueWith? one q = some v) :
    q.genus = 2 ∧ q.checkedEval U = some v := by
  cases h : divisorPairReduction? q with
  | none => simp only [divisorPairValueWith?, h, reduceCtorEq] at hv
  | some pair =>
    obtain ⟨d, s⟩ := pair
    obtain ⟨hd, last, hq⟩ := divisorPairReduction?_sound q h
    have hg : q.genus = 2 := congrArg SurfaceQuery.genus hq
    refine ⟨hg, ?_⟩
    rw [SurfaceQuery.checkedEval_of_geometricDomain U q (Or.inr (by
      simp only [StableArity, hg]; omega))]
    have hc := divisorPairValueWith?_of_singletons one q d s _ _ h
      (fun _ ↦ hid _ _) (fun _ ↦ hid _ _)
    exact (congrArg some ((congrArg (SurfaceQuery.eval U) hq).trans
      (eval_divisorPair U T laws H hpair last q.beta d hd s))).trans (hc.symm.trans hv)

end AxiomaticGW.SurfaceGenusTwo
