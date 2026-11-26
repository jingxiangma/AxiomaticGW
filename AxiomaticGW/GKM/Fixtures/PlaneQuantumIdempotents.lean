/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneSmallQuantumProduct
public import Mathlib.Algebra.DualNumber
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# The three primitive plane idempotents through first Novikov order

Use the dual numbers over the actual localized torus field, with the nilpotent
parameter representing the full effective line class. Each classical root moves
by the inverse fixed-point Euler factor. Evaluation at the three lifted roots is
bijective. Its inverse gives a unique lift of every classical fixed-point projector.
-/

@[expose] public section
namespace AxiomaticGW.GKM.PlaneQuantumIdempotents
open EquivariantCoefficients PlaneSmallQuantumProduct
open scoped DualNumber
noncomputable section

abbrev D := DualNumber Coefficient
abbrev lift (s : Coefficient) : D := TrivSqZeroExt.inl s

def euler (i : Fin 3) : Coefficient := SurfaceFrames.Plane.request.euler i

theorem euler_ne (i : Fin 3) : euler i ≠ 0 := by
  simpa only [euler, ← SurfaceReplay.Plane.accepted.euler_eq] using
    SurfaceReplay.Plane.accepted.euler_ne_zero i

/-- A root of the quantum cubic with linear coefficient 1/Euler. -/
def root (i : Fin 3) : D := ⟨classicalRoot i, (euler i)⁻¹⟩

theorem root_equation (i : Fin 3) :
    root i * (root i + lift x) * (root i + lift y) = ε := by
  apply TrivSqZeroExt.ext
  · change classicalRoot i * (classicalRoot i + x) * (classicalRoot i + y) = 0
    fin_cases i <;> simp [classicalRoot]
  · have hder : (classicalRoot i + x) * (classicalRoot i + y) +
        classicalRoot i * (classicalRoot i + y) + classicalRoot i * (classicalRoot i + x) =
        euler i := by
      fin_cases i <;> dsimp [euler, SurfaceFrames.Plane.request, classicalRoot] <;> ring
    simp only [DualNumber.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.snd_eps,
      add_zero, lift, root]
    rw [TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk]
    linear_combination (norm := ring_nf) (euler i)⁻¹ * hder +
      inv_mul_cancel₀ (euler_ne i)

/-- The same polynomial multiplication as the accepted three-point comparison,
with q the square-zero line parameter. -/
def multiply : State D → State D → State D := product (lift x) (lift y) ε

def spectrum (a : State D) (i : Fin 3) : D := evaluate (lift x) (root i) a

theorem spectrum_mul (a b : State D) :
    spectrum (multiply a b) = spectrum a * spectrum b := by
  funext i
  exact evaluate_mul _ _ _ _ (root_equation i) _ _

/-- First derivative of evaluation in the toric frame of the accepted state space. -/
def derivative (a : State Coefficient) (i : Fin 3) : Coefficient :=
  (euler i)⁻¹ * (a 1 + (2 * classicalRoot i + x) * a 2)

abbrev constantPart (a : State D) : State Coefficient := fun i ↦ (a i).fst
abbrev linePart (a : State D) : State Coefficient := fun i ↦ (a i).snd

theorem spectrum_constant (a : State D) :
    constantPart (spectrum a) = pointEquiv (constantPart a) := by
  funext i
  rw [restrict_evaluate]
  rfl

theorem spectrum_line (a : State D) :
    linePart (spectrum a) = pointEquiv (linePart a) + derivative (constantPart a) := by
  funext i
  rw [Pi.add_apply, restrict_evaluate]
  simp only [linePart, constantPart, spectrum, evaluate, derivative, TrivSqZeroExt.snd_add,
    DualNumber.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add,
    lift, root, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_mk,
    TrivSqZeroExt.snd_mk]
  ring

/-- Reconstruct basis coordinates over the dual numbers from the three lifted fixed evaluations. -/
def interpolate (z : State D) (i : Fin 3) : D :=
  let a := pointEquiv.symm (constantPart z)
  ⟨a i, pointEquiv.symm (linePart z - derivative a) i⟩

theorem spectrum_interpolate (z : State D) : spectrum (interpolate z) = z := by
  funext i
  apply TrivSqZeroExt.ext
  · have hs := spectrum_constant (interpolate z)
    change constantPart (spectrum (interpolate z)) =
      pointEquiv (pointEquiv.symm (constantPart z)) at hs
    rw [pointEquiv.apply_symm_apply] at hs
    exact congrFun hs i
  · have hs := spectrum_line (interpolate z)
    change linePart (spectrum (interpolate z)) =
      pointEquiv (pointEquiv.symm (linePart z - derivative (pointEquiv.symm (constantPart z)))) +
      derivative (pointEquiv.symm (constantPart z)) at hs
    rw [pointEquiv.apply_symm_apply, sub_add_cancel] at hs
    exact congrFun hs i

theorem spectrum_injective : Function.Injective spectrum := by
  intro a b he
  have hc := congrArg constantPart he
  rw [spectrum_constant, spectrum_constant] at hc
  have h0 := pointEquiv.injective hc
  have hs := congrArg linePart he
  rw [spectrum_line, spectrum_line, h0] at hs
  have h1 := pointEquiv.injective (add_right_cancel hs)
  funext i
  exact TrivSqZeroExt.ext (congrFun h0 i) (congrFun h1 i)

/-- The unique lift with value one at its own quantum root and zero at both others. -/
def projector (i : Fin 3) : State D := interpolate (Pi.single i 1)

theorem projector_spectrum (i : Fin 3) : spectrum (projector i) = Pi.single i 1 :=
  spectrum_interpolate _

theorem projector_constant (i : Fin 3) :
    constantPart (projector i) = pointEquiv.symm (Pi.single i 1) := by
  change pointEquiv.symm (constantPart (Pi.single i 1)) = _
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp only [constantPart, Pi.single_eq_same, TrivSqZeroExt.fst_one]
  · simp only [constantPart, Pi.single_eq_of_ne h, TrivSqZeroExt.fst_zero]

/-- The linear correction to each classical primitive projector, expressed through
the inverse of the already certified restriction matrix. -/
theorem projector_line (i : Fin 3) : linePart (projector i) =
    -pointEquiv.symm (derivative (pointEquiv.symm (Pi.single i 1))) := by
  have hs := spectrum_line (projector i)
  rw [projector_spectrum, projector_constant] at hs
  have hzero : linePart (Pi.single i 1 : State D) = 0 := by
    funext j
    by_cases h : j = i <;> simp [linePart, h]
  rw [hzero] at hs
  apply pointEquiv.injective
  rw [map_neg, pointEquiv.apply_symm_apply]
  exact eq_neg_of_add_eq_zero_left hs.symm

theorem projector_mul (i j : Fin 3) :
    multiply (projector i) (projector j) = if i = j then projector i else 0 := by
  apply spectrum_injective
  rw [spectrum_mul, projector_spectrum, projector_spectrum]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, projector_spectrum]
    funext k
    by_cases hk : k = i <;> simp [hk]
  · rw [if_neg h]
    funext k
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp_all [spectrum, evaluate]

theorem projector_sum : ∑ i : Fin 3, projector i = ![1,0,0] := by
  apply spectrum_injective
  funext j
  have hsum : spectrum (∑ i : Fin 3, projector i) j = ∑ i : Fin 3, spectrum (projector i) j := by
    simp only [spectrum, evaluate, Finset.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  simp only [projector_spectrum, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [spectrum, evaluate]

/-- The first projector has an actual nonzero first-order coefficient in the
original toric basis. Its classical representative is (H+x)(H+y)/(xy). -/
theorem projector_zero_moves : linePart (projector 0) ≠ 0 := by
  have hclass : pointEquiv.symm (Pi.single 0 1) = ![1, x⁻¹, (x*y)⁻¹] := by
    apply pointEquiv.injective
    rw [pointEquiv.apply_symm_apply]
    funext i
    rw [restrict_evaluate]
    fin_cases i <;> simp +decide [classicalRoot, evaluate, Matrix.cons_val_two]
    all_goals field_simp [x_ne_zero, y_ne_zero]
    all_goals ring
  intro hz
  have hs := congrFun (spectrum_line (projector 0)) 1
  rw [projector_spectrum, hz, map_zero, zero_add, projector_constant, hclass] at hs
  have hleft : linePart (Pi.single 0 1 : State D) 1 = 0 := by
    simp +decide [linePart]
  rw [hleft] at hs
  change 0 = (euler 1)⁻¹ * (x⁻¹ + (2 * -y + x) * (x*y)⁻¹) at hs
  have h : x⁻¹ + (2 * -y + x) * (x*y)⁻¹ = (x-y) / (x*y) := by
    field_simp [x_ne_zero, y_ne_zero]
    ring
  rw [h] at hs
  exact (mul_ne_zero (inv_ne_zero (euler_ne 1))
    (div_ne_zero x_sub_y_ne_zero (mul_ne_zero x_ne_zero y_ne_zero))) hs.symm

private theorem scalar_idempotent (a : D) (ha : a * a = a) : a = 0 ∨ a = 1 := by
  have hc := congrArg TrivSqZeroExt.fst ha
  have hs := congrArg TrivSqZeroExt.snd ha
  rw [TrivSqZeroExt.fst_mul] at hc
  rw [DualNumber.snd_mul] at hs
  have h : a.fst * (a.fst - 1) = 0 := by rw [mul_sub, hc, mul_one, sub_self]
  rcases mul_eq_zero.mp h with hz | h1
  · rw [hz, zero_mul, mul_zero, add_zero] at hs
    exact Or.inl (TrivSqZeroExt.ext hz hs.symm)
  · have h1 := sub_eq_zero.mp h1
    rw [h1, one_mul, mul_one] at hs
    exact Or.inr (TrivSqZeroExt.ext h1 (by change a.snd = 0; linear_combination hs))

/-- Each factor has only the two scalar idempotents, so the lifted fixed-point
projectors are primitive inside the deformed algebra. -/
theorem projector_primitive (i : Fin 3) (a : State D)
    (ha : multiply a a = a) (hs : multiply a (projector i) = a) :
    a = 0 ∨ a = projector i := by
  have h0 := congrArg spectrum ha
  have h1 := congrArg spectrum hs
  rw [spectrum_mul] at h0
  rw [spectrum_mul, projector_spectrum] at h1
  have hoff (j : Fin 3) (hj : j ≠ i) : spectrum a j = 0 := by
    have hj' := congrFun h1 j
    rw [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero] at hj'
    exact hj'.symm
  rcases scalar_idempotent (spectrum a i) (congrFun h0 i) with hz | hu
  · left
    apply spectrum_injective
    funext j
    by_cases hj : j = i
    · subst j
      simpa [spectrum, evaluate] using hz
    · simpa [spectrum, evaluate] using hoff j hj
  · right
    apply spectrum_injective
    rw [projector_spectrum]
    funext j
    by_cases hj : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hu
    · simpa only [Pi.single_eq_of_ne hj] using hoff j hj

end
end AxiomaticGW.GKM.PlaneQuantumIdempotents
