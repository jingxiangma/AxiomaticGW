/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.ExceptionalGenusTwoVertexValues
public import AxiomaticGW.GKM.Fixtures.ExceptionalBoundaryData
public import AxiomaticGW.Surfaces.DimensionVanishing
public import Mathlib.Tactic.FieldSimp

/-! # A nonconstant genus-two localization sum on the exceptional curve

For τ₃(E₁) in class E₁ of the two-point blowup, the three genus distributions
and the two marked endpoints give six terms. The genus-one split vanishes by the
dimension of the marked vertex. The remaining terms use the ten genus-two Hodge
integrals recorded by the pinned producer, with both tangent directions retained.
-/

@[expose] public section
namespace AxiomaticGW.GKM.ExceptionalGenusTwoCubic
open EquivariantCoefficients GenusTwoVertexHodgeReduction
noncomputable section

/-- The original ordered positive-degree query. -/
def request : SurfaceQuery .blowupTwo := ⟨2, ![1, 0, 0], [⟨.exceptional 0, 3⟩]⟩

/-- Cotangent degree left for the flag and the two λ indices at a genus-two vertex. -/
def available (marked : Bool) : ℕ := if marked then 2 else 4

/-- Signed vertex coefficient for the two ordered tangent Hodge indices. -/
def hodge (marked : Bool) (i j : Fin 3) : ℚ :=
  let d := available marked
  let k := d - i.val - j.val
  if i.val + j.val ≤ d then
    (-1) ^ (i.val + j.val) * evaluate ExceptionalGenusTwoVertexValues.seed
      (min i j) (max i j) (min_le_max) (if marked then [k, 3] else [k])
  else 0

/-- Sum over the Hodge exponent in the direction tangent to the edge. -/
def column (marked : Bool) (j : Fin 3) : ℚ := ∑ i : Fin 3, hodge marked i j

/-- The cancellations at each transverse Hodge exponent are checked over the rationals. -/
theorem columns : (∀ j, column false j = ![0, 0, 1 / 1152] j) ∧
    (∀ j, column true j = ![0, -11 / 2880, 7 / 5760] j) := by decide +kernel

/-- Every retained Hodge integral occurs in the held native call ledger. -/
theorem hits_native : ∀ (m : Bool) (i j : Fin 3), i.val + j.val ≤ available m →
    let k := available m - i.val - j.val
    let p := if m then [k, 3] else [k]
    (min i j, max i j, p, (-1 : ℚ) ^ (i.val + j.val) * hodge m i j) ∈
      ExceptionalGenusTwoVertexValues.vertices := by decide +kernel

/-- Cancel the tangent factor against the flag cotangent expansion for each admissible term. -/
theorem flag_monomial (w t : Coefficient) (hw : w ≠ 0) (d i j : ℕ) (h : i + j ≤ d) :
    w ^ ((1 : ℤ) - i) * t ^ ((1 : ℤ) - j) *
      w ^ (-((d-i-j : ℕ) : ℤ)-1) = t ^ ((1 : ℤ) - j) / w ^ (d-j) := by
  have hz : (1 : ℤ) - i + (-((d-i-j : ℕ) : ℤ)-1) = -((d-j : ℕ) : ℤ) := by omega
  rw [mul_right_comm, ← zpow_add₀ hw, hz, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]

/-- Stable genus-two vertex at flag character w and transverse character t. -/
def stableVertex (marked : Bool) (w t : Coefficient) : Coefficient :=
  ∑ j : Fin 3, (column marked j : Coefficient) * t ^ ((1 : ℤ) - j.val) /
    w ^ (available marked - j.val)

/-- Expand the two ordered tangent λ factors and every possible cotangent power on the flag.
The two tangent powers and the inverse flag power are those in the original vertex formula. -/
theorem stable_expansion (m : Bool) (w t : Coefficient) (hw : w ≠ 0) :
    stableVertex m w t = ∑ j : Fin 3, ∑ i : Fin 3, (hodge m i j : Coefficient) *
      (w ^ ((1 : ℤ) - i.val) * t ^ ((1 : ℤ) - j.val) *
        w ^ (-((available m - i.val - j.val : ℕ) : ℤ) - 1)) := by
  unfold stableVertex
  apply Finset.sum_congr rfl
  intro j _
  simp only [column, Rat.cast_sum, Finset.sum_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val + j.val ≤ available m
  · rw [flag_monomial w t hw _ _ _ hi, div_eq_mul_inv, mul_assoc]
  · simp only [hodge, if_neg hi, Rat.cast_zero, zero_mul]

/-- The unmarked and marked stable vertices after collecting the signed Hodge coefficients. -/
theorem stable_form (w t : Coefficient) (hw : w ≠ 0) (ht : t ≠ 0) :
    stableVertex false w t = 1 / (1152 * t * w ^ 2) ∧
    stableVertex true w t = -11 / (2880 * w) + 7 / (5760 * t) := by
  constructor <;>
    simp only [stableVertex, Fin.sum_univ_three, columns.1, columns.2, available,
      Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.tail_cons] <;>
    norm_num <;> field_simp

/-- Product of the actual primitive edge and tangent-normalization factors. -/
theorem edge_tangent : (ExceptionalBoundaryData.factors .first).edge *
    (ExceptionalBoundaryData.factors .first).tangent = x * y := by
  have hn : x ^ 2 - 2*x*y + y ^ 2 ≠ 0 := by
    rw [show x ^ 2 - 2*x*y + y ^ 2 = (x-y)^2 by ring]
    exact pow_ne_zero _ x_sub_y_ne_zero
  dsimp only [ExceptionalBoundaryData.factors]
  rw [div_mul_eq_mul_div, div_eq_iff hn]
  ring

/-- The stable genus-two vertex and opposite unstable rational vertex, with the actual
edge, normalization and exceptional-divisor restriction at the marked end. -/
def atEnds (marked : Bool) (w t u : Coefficient) : Coefficient :=
  (ExceptionalBoundaryData.factors .first).edge * (ExceptionalBoundaryData.factors .first).tangent *
    (if marked then t else u) * stableVertex marked w t *
    ((if marked then -w else (-(-w)) ^ 3) / ((-w) * u))

/-- A locus is indexed by the genus on the source end and the endpoint of its marking.
For genus split (1,1), τ₃ exceeds dimension two on the marked elliptic vertex. -/
def contribution (g : Fin 3) (m : Fin 2) : Coefficient :=
  if g = 1 then 0 else
  let w := if g = 2 then x - y else y - x
  let t := if g = 2 then y else x
  let u := if g = 2 then x else y
  let marked := decide ((g = 2 ∧ m = 0) ∨ (g = 0 ∧ m = 1))
  atEnds marked w t u

/-- After summing the six fixed loci the poles cancel to a linear two-character polynomial. -/
theorem sum_loci : (∑ g : Fin 3, ∑ m : Fin 2, contribution g m) = (x + y) / 240 := by
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]
  change atEnds false (y-x) x y + atEnds true (y-x) x y + (0+0) +
    (atEnds true (x-y) y x + atEnds false (x-y) y x) = _
  simp only [atEnds, edge_tangent, Bool.false_eq_true, if_false, if_true, add_zero, neg_neg,
    (stable_form _ _ x_sub_y_ne_zero y_ne_zero).1,
    (stable_form _ _ x_sub_y_ne_zero y_ne_zero).2,
    (stable_form _ _ y_sub_x_ne_zero x_ne_zero).1, (stable_form _ _ y_sub_x_ne_zero x_ne_zero).2]
  rw [show y - x = -(x - y) by abel]
  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero]
  ring

/-- Ordinary reconstruction at this query requires only the surface grading. -/
theorem ordinary : request.dimensionVanishing? = some 0 := by decide +kernel

end
end AxiomaticGW.GKM.ExceptionalGenusTwoCubic
