/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1FiberBPScalar
public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CertifiedPoints

/-!
# Class-zero divisor coefficients of the three remaining F1 fiber equations

Each entry uses the original scalar BP row at its full curve class. The N
equation uses four ordered triples at the shifted source E+F, combined with
the coefficients of the existing reconstruction. The terminal rational
calculation uses the certified genus-zero primary point function.
-/

@[expose] public section
namespace AxiomaticGW.BlowupF1FiberBPValues
open SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar
open BlowupF1FiberHReduction BlowupF1FiberHZeroCoefficients
open BlowupF1FiberHTwoFlagZero BlowupF1FiberBPCoefficients

set_option maxRecDepth 20000

private def triples : Fin 6 → Fin 3 → Fin 2 :=
  ![![0, 0, 0], ![1, 1, 1], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1], ![0, 0, 0]]

private def source (j : Fin 6) : target.Curve := if j < 2 then fiber else ![1, 1]

private def points (j : Fin 6) : ℕ := if j < 2 then 1 else 2

private def entries : Fin 6 → Fin 2 → ℚ :=
  ![![12, -12], ![12, -12], ![0, 0], ![0, 0], ![0, 0], ![12, 0]]

private theorem computed (j : Fin 6) (r : Fin 2) :
    BelorousskiPandharipande.pointCoefficient target (points j) (source j)
      (requested ∘ triples j) (zeroVariable (requested r)) = entries j r := by
  have hn : points j ≤ 2 := by unfold points; split <;> decide
  rw [← oneFlagCoefficient_eq r _ hn, oneFlagCoefficient_scalar r _ hn,
    ← BlowupF1CertifiedPoints.rational_eq]
  revert j r
  decide +kernel

private theorem map_triple (b c d : Fin 2) :
    requested ∘ (![b, c, d] : Fin 3 → Fin 2) = ![requested b, requested c, requested d] := by
  funext i
  fin_cases i <;> rfl

private theorem column (r : Fin 2) :
    (zeroVariable (requested r)) = if r = 0 then hZero else kZero := by
  fin_cases r <;> decide +kernel

private theorem at_request (j : Fin 6) (r : Fin 2) :
    BelorousskiPandharipande.pointCoefficient target (points j) (source j)
      ![requested (triples j 0), requested (triples j 1), requested (triples j 2)]
      (if r = 0 then hZero else kZero) = entries j r := by
  rw [← column, ← map_triple]
  have he : ![triples j 0, triples j 1, triples j 2] = triples j := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact computed j r

/-- The complete P row has the two indicated class-zero divisor columns. -/
theorem p_coefficients : singletonCoefficient 0 (fiber, .point) hZero = 12 ∧
    singletonCoefficient 0 (fiber, .point) kZero = -12 :=
  ⟨at_request 0 0, at_request 0 1⟩

/-- The complete exceptional K row uses the distinct all-exceptional triple. -/
theorem k_coefficients : singletonCoefficient 0 (fiber, .exceptional 0) hZero = 12 ∧
    singletonCoefficient 0 (fiber, .exceptional 0) kZero = -12 :=
  ⟨at_request 1 0, at_request 1 1⟩

private theorem primary_column (r : Fin 2) :
    singletonCoefficient 0 (fiber, .primary) (if r = 0 then hZero else kZero) =
      (if r = 0 then -4 else 0) := by
  have he : target.effective.energy fiber = 2 := by decide +kernel
  have hd : target.planeDegree fiber = 1 := by decide +kernel
  have hs : fiber + target.exceptionalCurve 0 = ![1, 1] := by decide +kernel
  simp only [singletonCoefficient, he, hd, hs, Nat.cast_one, mul_one]
  let coeff (j : Fin 6) := BelorousskiPandharipande.pointCoefficient target
    (points j) (source j) ![requested (triples j 0), requested (triples j 1),
      requested (triples j 2)] (if r = 0 then hZero else kZero)
  change 3 / 2 * coeff 2 + (-1) * coeff 3 + 1 / 2 * coeff 4 + (-1 / 3) * coeff 5 = _
  have hc (j : Fin 6) : coeff j = entries j r := at_request j r
  simp only [hc]
  fin_cases r <;> decide +kernel

/-- The shifted primary combination includes all four original rational weights. -/
theorem n_coefficients : singletonCoefficient 0 (fiber, .primary) hZero = -4 ∧
    singletonCoefficient 0 (fiber, .primary) kZero = 0 :=
  ⟨primary_column 0, primary_column 1⟩

end AxiomaticGW.BlowupF1FiberBPValues
