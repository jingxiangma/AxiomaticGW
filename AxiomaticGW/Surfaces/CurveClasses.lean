/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Coefficients.WeightedCurveClass
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Curve coordinates for the fixed surface applications

The three required targets use the effective generators `H`, `(E,F)`, and
`(E₁,E₂,L)`, respectively, where `F = H-E` and `L = H-E₁-E₂`.
The integer lattice coordinates retain the coefficient of each exceptional
divisor, including negative coefficients. Their identification with geometric
effective curve classes is a separate input obligation.
-/

@[expose] public section

namespace AxiomaticGW

/-- The fixed first research applications, not an extensible target oracle. -/
inductive SurfaceTarget
  | plane
  | hirzebruchOne
  | blowupTwo
  deriving DecidableEq, Repr

namespace SurfaceTarget

/-- Number of exceptional divisors in the chosen blowup description. -/
abbrev blowups : SurfaceTarget → ℕ
  | plane => 0
  | hirzebruchOne => 1
  | blowupTwo => 2

/-- Effective generator multiplicities. Their order is documented above. -/
abbrev Curve (X : SurfaceTarget) := Fin (X.blowups + 1) → ℕ

/-- Anticanonical weights on the chosen effective generators. -/
def weights : (X : SurfaceTarget) → Fin (X.blowups + 1) → ℕ
  | plane => ![3]
  | hirzebruchOne => ![1, 2]
  | blowupTwo => ![1, 1, 1]

theorem weights_pos (X : SurfaceTarget) (i : Fin (X.blowups + 1)) : 0 < X.weights i := by
  cases X <;> fin_cases i <;> decide

/-- The locally finite coordinate monoid, with anticanonical energy. -/
def effective (X : SurfaceTarget) : EffectiveCurveMonoid X.Curve :=
  WeightedCurveClass.effective X.weights X.weights_pos

/-- Executable enumeration of all classes up to an anticanonical bound. -/
def bounded (X : SurfaceTarget) (d : ℕ) : Finset X.Curve :=
  WeightedCurveClass.bounded X.weights d

theorem bounded_eq (X : SurfaceTarget) (d : ℕ) :
    X.bounded d = X.effective.bounded d :=
  WeightedCurveClass.bounded_eq X.weights X.weights_pos d

/-- Executable ordered class splittings, including zero and exceptional parts. -/
def splittings (X : SurfaceTarget) (beta : X.Curve) : Finset (X.Curve × X.Curve) :=
  WeightedCurveClass.splittings beta

theorem splittings_eq (X : SurfaceTarget) (beta : X.Curve) :
    X.splittings beta = X.effective.splittings beta :=
  WeightedCurveClass.splittings_eq X.weights X.weights_pos beta

/-- Coordinates in the integer basis `(H,E₁,...,Eᵣ)`. The exceptional
coordinates are coefficients of `Eᵢ`, not their negated multiplicities. -/
def latticeCoordinates : (X : SurfaceTarget) → X.Curve → Fin (X.blowups + 1) → ℤ
  | plane, beta => ![(beta 0 : ℤ)]
  | hirzebruchOne, beta => ![(beta 1 : ℤ), (beta 0 : ℤ) - beta 1]
  | blowupTwo, beta => ![(beta 2 : ℤ), (beta 0 : ℤ) - beta 2, (beta 1 : ℤ) - beta 2]

/-- Inverse change of integer coordinates, before imposing effectivity. -/
def generatorCoordinates : (X : SurfaceTarget) →
    (Fin (X.blowups + 1) → ℤ) → Fin (X.blowups + 1) → ℤ
  | plane, c => ![c 0]
  | hirzebruchOne, c => ![c 1 + c 0, c 0]
  | blowupTwo, c => ![c 1 + c 0, c 2 + c 0, c 0]

theorem generatorCoordinates_latticeCoordinates (X : SurfaceTarget) (beta : X.Curve) :
    X.generatorCoordinates (X.latticeCoordinates beta) = fun i ↦ (beta i : ℤ) := by
  cases X
  · funext i
    fin_cases i
    rfl
  · funext i
    fin_cases i
    · change (beta 0 : ℤ) - beta 1 + beta 1 = beta 0
      ring
    · rfl
  · funext i
    fin_cases i
    · change (beta 0 : ℤ) - beta 2 + beta 2 = beta 0
      ring
    · change (beta 1 : ℤ) - beta 2 + beta 2 = beta 1
      ring
    · rfl


/-- Full curve coordinates, unlike energy alone, distinguish all classes. -/
theorem latticeCoordinates_injective (X : SurfaceTarget) :
    Function.Injective X.latticeCoordinates := by
  intro a b h
  have hc := congrArg X.generatorCoordinates h
  rw [generatorCoordinates_latticeCoordinates, generatorCoordinates_latticeCoordinates] at hc
  funext i
  exact Int.ofNat_inj.mp (congrFun hc i)

theorem latticeCoordinates_add (X : SurfaceTarget) (a b : X.Curve) :
    X.latticeCoordinates (a + b) = X.latticeCoordinates a + X.latticeCoordinates b := by
  cases X
  · funext i
    fin_cases i
    exact Nat.cast_add _ _
  · funext i
    fin_cases i
    · exact Nat.cast_add _ _
    · change ((a 0 + b 0 : ℕ) : ℤ) - (a 1 + b 1 : ℕ) =
        ((a 0 : ℤ) - a 1) + ((b 0 : ℤ) - b 1)
      simp only [Nat.cast_add]
      ring
  · funext i
    fin_cases i
    · exact Nat.cast_add _ _
    · change ((a 0 + b 0 : ℕ) : ℤ) - (a 2 + b 2 : ℕ) =
        ((a 0 : ℤ) - a 2) + ((b 0 : ℤ) - b 2)
      simp only [Nat.cast_add]
      ring
    · change ((a 1 + b 1 : ℕ) : ℤ) - (a 2 + b 2 : ℕ) =
        ((a 1 : ℤ) - a 2) + ((b 1 : ℤ) - b 2)
      simp only [Nat.cast_add]
      ring


/-- Intersection numbers with `(H,E₁,...,Eᵣ)`, using diagonal form `(1,-1,...)`. -/
def divisorIntersections (X : SurfaceTarget) (beta : X.Curve) :
    Fin (X.blowups + 1) → ℤ :=
  fun i ↦ if i = 0 then X.latticeCoordinates beta i else -X.latticeCoordinates beta i

/-- First-Chern degree of a coordinate class. -/
def c1Degree (X : SurfaceTarget) : X.Curve →+ ℤ :=
  (Nat.castAddMonoidHom ℤ).comp X.effective.energy

/-- The coordinate energy equals intersection with `3H - ∑ Eᵢ`. -/
theorem c1Degree_eq_intersection (X : SurfaceTarget) (beta : X.Curve) :
    X.c1Degree beta =
      3 * X.divisorIntersections beta 0 -
        ∑ i : Fin X.blowups, X.divisorIntersections beta i.succ := by
  change ((∑ i, X.weights i * beta i : ℕ) : ℤ) = _
  cases X
  · change ((∑ i : Fin 1, (![3] : Fin 1 → ℕ) i * beta i : ℕ) : ℤ) =
      3 * (beta 0 : ℤ) - ∑ i : Fin 0, _
    norm_num [Fin.sum_univ_one]
  · change ((∑ i : Fin 2, (![1, 2] : Fin 2 → ℕ) i * beta i : ℕ) : ℤ) =
      3 * (beta 1 : ℤ) - ∑ i : Fin 1, _
    rw [Fin.sum_univ_two, Fin.sum_univ_one]
    change ((1 * beta 0 + 2 * beta 1 : ℕ) : ℤ) =
      3 * (beta 1 : ℤ) - -((beta 0 : ℤ) - beta 1)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  · change ((∑ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i * beta i : ℕ) : ℤ) =
      3 * (beta 2 : ℤ) - ∑ i : Fin 2, _
    rw [Fin.sum_univ_three, Fin.sum_univ_two]
    change ((1 * beta 0 + 1 * beta 1 + 1 * beta 2 : ℕ) : ℤ) =
      3 * (beta 2 : ℤ) - (-((beta 0 : ℤ) - beta 2) + -((beta 1 : ℤ) - beta 2))
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring

end SurfaceTarget

end AxiomaticGW
