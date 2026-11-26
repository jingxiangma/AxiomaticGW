/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoUnitPairs
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingTransfer

/-! # Two-marked descendant divisor reduction on a surface

The primary divisor multiplies the unchanged singleton by its intersection with the full
curve class. The correction lowers the other power by one and cups its state with the
divisor. In particular H² is the point and Eᵢ² is minus the point.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceFirstDescendant
variable {X : SurfaceTarget}

/-- Coefficient and basis state obtained by cupping the surviving input with a divisor. -/
def divisorCup (d a : SurfaceBasisLabel X) : ℚ × SurfaceBasisLabel X :=
  if a = .unit then (1, d) else (divisorIntersection a d, .point)

/-- The divisor correction exists only when the original cotangent power is positive. -/
def cupCoefficient (d : SurfaceBasisLabel X) (s : SurfaceInsertion X) : ℚ :=
  if s.psi = 0 then 0 else (divisorCup d s.label).1

/-- The second singleton carries the cup product state and one fewer psi power. -/
def cupInsertion (d : SurfaceBasisLabel X) (s : SurfaceInsertion X) : SurfaceInsertion X :=
  ⟨(divisorCup d s.label).2, s.psi - 1⟩

/-- Ordered query placing a primary divisor before or after the surviving insertion. -/
def divisorPair (last : Bool) (beta : X.Curve) (d : SurfaceBasisLabel X)
    (s : SurfaceInsertion X) : SurfaceQuery X :=
  ⟨2, beta, if last then [s, ⟨d, 0⟩] else [⟨d, 0⟩, s]⟩

private theorem divisorCup_value (d a : SurfaceBasisLabel X) (hd : d.codimension = 1) :
    d.value * a.value = (divisorCup d a).1 • (divisorCup d a).2.value := by
  by_cases ha : a = .unit
  · subst a
    simp only [divisorCup, if_true, SurfaceBasisLabel.value, mul_one, one_smul]
  · simpa only [divisorCup, if_neg ha] using value_mul_of_divisor a d ha hd

variable {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    {F : ForgetfulPushforward C I} {A : GWDivisorAxiom Omega F} {L : DescendantDivisorLaw M I A}

/-- Both signed singleton terms of the stable-map divisor equation at genus two. -/
theorem eval_divisorPair (U : UnstableDescendantConventions M I)
    (T : SurfaceTheoryIdentification X Omega) (laws : DescendantStringDilatonLaws M I)
    (H : FullDescendantDivisorLaw U L) (hpair : T.DivisorPairingCompatible A)
    (last : Bool) (beta : X.Curve) (d : SurfaceBasisLabel X) (hd : d.codimension = 1)
    (s : SurfaceInsertion X) :
    (divisorPair last beta d s).eval U =
      d.primaryFactor beta * SurfaceQuery.eval U ⟨2, beta, [s]⟩ +
      cupCoefficient d s * SurfaceQuery.eval U ⟨2, beta, [cupInsertion d s]⟩ := by
  let div : X.Divisor := ⟨d.value, by
    change d.value ∈ SurfaceCohomology.degree X.blowups 1
    rw [← hd]; exact d.value_mem_degree⟩
  have hβ : A.divisorPairing (T.divisor div) beta = d.primaryFactor beta := by
    rw [hpair]
    cases d with
    | unit => norm_num only [SurfaceBasisLabel.codimension] at hd
    | point => norm_num only [SurfaceBasisLabel.codimension] at hd
    | hyperplane => exact X.divisorPairing_hyperplane beta
    | exceptional i => exact X.divisorPairing_exceptional i beta
  have hs : StableArity 2 (Fin 1) := by simp only [StableArity, Fintype.card_fin]; decide
  have he := H.global_divisor 2 (Fin 1) beta (fun _ ↦ s.psi) (fun _ ↦ s.label.value) (T.divisor div)
  rw [divisorCorrection_eq_zero_of_stable _ _ _ _ _ _ _ _ _ hs, add_zero, hβ,
    Fintype.sum_unique, T.divisorAction_eq_mul U laws L] at he
  rw [divisorPair, eval_ordered_pair, eval_singleton_marking, eval_singleton_marking]
  have hleft : U.invariant 2 (Option (Fin 1)) beta
      (fun | none => 0 | some _ => s.psi) (fun | none => d.value | some _ => s.label.value) =
      d.primaryFactor beta * U.invariant 2 (Fin 1) beta (fun _ ↦ s.psi) (fun _ ↦ s.label.value) +
      (if s.psi = 0 then 0 else U.invariant 2 (Fin 1) beta
        (lowerPower (fun _ ↦ s.psi) default)
        (replaceInput (fun _ ↦ s.label.value) default (d.value * s.label.value))) := by
    convert! he using 1
    congr 1 <;> funext i <;> cases i <;> rfl
  trans U.invariant 2 (Option (Fin 1)) beta
    (fun | none => 0 | some _ => s.psi) (fun | none => d.value | some _ => s.label.value)
  · congr 1
  rw [hleft]
  congr 1
  by_cases hp : s.psi = 0
  · rw [if_pos hp, cupCoefficient, if_pos hp, zero_mul]
  · rw [if_neg hp, cupCoefficient, if_neg hp, divisorCup_value d s.label hd,
      replaceInput, ← U.invariantMap_apply, MultilinearMap.map_update_smul, smul_eq_mul,
      U.invariantMap_apply]
    congr 2 <;> funext i <;> rw [Subsingleton.elim i default]
    · rw [lowerPower, Function.update_self]; rfl
    · rw [Function.update_self]; rfl

end AxiomaticGW.SurfaceGenusTwo
