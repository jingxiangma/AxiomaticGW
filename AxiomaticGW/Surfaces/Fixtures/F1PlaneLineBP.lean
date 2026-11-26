/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.F1PlaneLineReduction

/-! # The HHH and EEE equations at the ordinary plane line in the one-point blowup

These two BP equations reuse the original fiber calculation at its shifted
class E + F. The HHH equation relates the point and hyperplane states, and
the EEE equation has vanishing same-class point coefficient because E · H = 0.
-/

@[expose] public section
namespace AxiomaticGW.F1PlaneLine
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupScalar
open BlowupF1CertifiedPoints BelorousskiPandharipande

set_option Elab.async false
set_option maxRecDepth 20000

private def sector : Fin 2 → Family X := ![.point, .exceptional 0]

private theorem triple (a : SurfaceBasisLabel X) : (![a,a,a] : Fin 3 → _) = fun _ ↦ a := by
  funext j
  fin_cases j <;> rfl

/-- The lower-genus HHH graph sum is the previously checked shifted fiber source. -/
theorem point_constant : constant 0 (line, .point) = 1/80 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (line, .point) rational elliptic
    rational_eq elliptic_eq]
  change lowerPointConstantWithPrimary X rational elliptic 2 line
    ![.hyperplane, .hyperplane, .hyperplane] = _
  rw [triple]
  exact BlowupF1FiberBPValues.n_hhh_constant_computed

/-- The lower-genus all-exceptional source at the same line has zero sum. -/
theorem exceptional_constant : constant 0 (line, .exceptional 0) = 0 := by
  rw [← SurfaceGenusTwoBlowupPointCache.constant_eq 0 (line, .exceptional 0) rational elliptic
    rational_eq elliptic_eq]
  change lowerPointConstantWithPrimary X rational elliptic 2 line
    ![.exceptional 0, .exceptional 0, .exceptional 0] = _
  rw [triple]
  exact BlowupF1FiberBPValues.n_eee_constant_computed

private def coeff (r : Fin 2) (c : X.Curve) (b : Fin 4) : ℚ :=
  singletonCoefficient 0 (line, sector r) (.inr ((families b).query c))

private def same : Fin 2 → Fin 4 → ℚ := ![![18,-18,0,0], ![0,0,0,-18]]

private theorem primary_column (r : Fin 2) : coeff r line 2 = 0 := by
  have h (a : SurfaceBasisLabel X) (ha : a.codimension = 1) :
      BelorousskiPandharipande.pointCoefficient X 2 line ![a,a,a]
        (.inr (SurfaceQuery.points X 2 line 4)) = 0 := by
    apply SurfaceGenusTwoBlowupNSourcePrimary.pointCoefficient_primary_divisors_at_class
    intro j
    fin_cases j <;> exact ha
  fin_cases r
  · exact h .hyperplane rfl
  · exact h (.exceptional 0) rfl

private theorem same_coeff (r : Fin 2) (b : Fin 4) : coeff r line b = same r b := by
  have he : 0 < X.effective.energy line := by decide +kernel
  have hp := primary_column r
  unfold coeff at hp ⊢
  rw [singletonCoefficient_eq]
  fin_cases r <;> fin_cases b
  · exact SurfaceGenusTwoBlowupPCoefficients.hyperplane_coefficient line he
  · exact (SurfaceGenusTwoBlowupPCoefficients.point_coefficient line he).trans (by decide +kernel)
  · rw [← singletonCoefficient_eq]
    exact hp
  · exact SurfaceGenusTwoBlowupPCoefficients.exceptional_coefficient line 0 he
  · exact (SurfaceGenusTwoBlowupKCoefficients.first_coefficient 0 line .hyperplane 3 he).trans
      (by decide +kernel)
  · exact (SurfaceGenusTwoBlowupKCoefficients.point_coefficient 0 line he).trans (by decide +kernel)
  · rw [← singletonCoefficient_eq]
    exact hp
  · exact SurfaceGenusTwoBlowupKCoefficients.exceptional_coefficient_self 0 line he

private theorem zero_coeff (r : Fin 2) :
    coeff r 0 0 = (![12,0] : Fin 2 → ℚ) r ∧ coeff r 0 3 = 0 := by
  let d := BlowupF1FiberHTwoFlagZero.requested
  have hc (r s : Fin 2) : BelorousskiPandharipande.pointCoefficient X 2 line
      (d ∘ (fun _ : Fin 3 ↦ r))
      (BlowupF1FiberHZeroCoefficients.zeroVariable (d s)) =
        if r = 0 ∧ s = 0 then 12 else 0 := by
    rw [← BlowupF1FiberBPCoefficients.oneFlagCoefficient_eq s 2 (by decide),
      BlowupF1FiberBPCoefficients.oneFlagCoefficient_scalar s 2 (by decide), ← rational_eq]
    fin_cases r <;> fin_cases s <;> decide +kernel
  have hd (r : Fin 2) : d ∘ (fun _ : Fin 3 ↦ r) = ![d r,d r,d r] := by
    funext i
    fin_cases i <;> rfl
  simp only [hd] at hc
  fin_cases r
  · exact ⟨hc 0 0, hc 0 1⟩
  · exact ⟨hc 1 0, hc 1 1⟩

/-- The point first descendant agrees with the hyperplane first descendant on H. -/
theorem point_eq_hyperplane : value (line, .point) = value (line, .hyperplane) := by
  have h := reduced_row (.point : Family X)
  change constant 0 (line, .point) - coeff 0 0 0 / 960 - coeff 0 0 3 / 2880 +
    ∑ b : Fin 4, coeff 0 line b * value (line, families b) = 0 at h
  rw [point_constant, (zero_coeff 0).1, (zero_coeff 0).2] at h
  simp only [same_coeff, Fin.sum_univ_four] at h
  change 1/80 - 12/960 - 0/2880 + (18 * value (line,.hyperplane) +
    -18 * value (line,.point) + 0 * value (line,.primary) +
    0 * value (line,.exceptional 0)) = 0 at h
  linarith only [h]

/-- The EEE pivot gives the absolute exceptional first descendant in class H. -/
theorem exceptional_value : value (line, .exceptional 0) = 0 := by
  have h := reduced_row (Family.exceptional (X := X) 0)
  change constant 0 (line, .exceptional 0) - coeff 1 0 0 / 960 - coeff 1 0 3 / 2880 +
    ∑ b : Fin 4, coeff 1 line b * value (line, families b) = 0 at h
  rw [exceptional_constant, (zero_coeff 1).1, (zero_coeff 1).2] at h
  simp only [same_coeff, Fin.sum_univ_four] at h
  change 0 - 0/960 - 0/2880 + (0 * value (line,.hyperplane) +
    0 * value (line,.point) + 0 * value (line,.primary) +
    -18 * value (line,.exceptional 0)) = 0 at h
  linarith only [h]

end AxiomaticGW.F1PlaneLine
