/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.SmallQuantumGeneratorData
public import AxiomaticGW.GKM.Fixtures.SurfaceReplay
public import AxiomaticGW.GW.SmallQuantumProduct

/-!
# Equivariant small quantum multiplication for the plane through line degree

In the held toric frame the point lift is H(H+x). The degree-one tensor is
the pinned localization result. The algebraic product below is polynomial
in q; the GW comparison established here covers only the coefficients at zero
and at the full effective line class. The unmodified equivariant metric raises
the final index.
-/

@[expose] public section
namespace AxiomaticGW.GKM.PlaneSmallQuantumProduct
open EquivariantCoefficients Matrix
abbrev State (R : Type*) := Fin 3 → R

section Ring
variable {R : Type*} [CommRing R]

/-- Multiplication in the toric frame 1, H, P subject to H(H+x)(H+y)=q. -/
def product (x y q : R) (a b : State R) : State R :=
  ![a 0 * b 0 + q * (a 1 * b 2 + a 2 * b 1 + (x-y) * a 2 * b 2),
    a 0 * b 1 + a 1 * b 0 - x * a 1 * b 1 + q * a 2 * b 2,
    a 0 * b 2 + a 2 * b 0 + a 1 * b 1 - y * (a 1 * b 2 + a 2 * b 1) +
      (y^2-x*y) * a 2 * b 2]

/-- The coefficient at the single effective line class. -/
def line (x y : R) (a b : State R) : State R :=
  ![a 1 * b 2 + a 2 * b 1 + (x-y) * a 2 * b 2, a 2 * b 2, 0]

theorem expansion (x y q : R) (a b : State R) :
    product x y q a b = product x y 0 a b + q • line x y a b := by
  funext i
  fin_cases i <;> simp [product, line, mul_assoc]

/-- The unchanged metric is the top coordinate of classical multiplication. -/
def metric (x y : R) (a b : State R) : R := product x y 0 a b 2

theorem product_comm (x y q : R) (a b : State R) :
    product x y q a b = product x y q b a := by
  funext i
  fin_cases i <;> simp [product] <;> ring

theorem product_assoc (x y q : R) (a b c : State R) :
    product x y q (product x y q a b) c = product x y q a (product x y q b c) := by
  funext i
  fin_cases i <;> simp [product] <;> ring

theorem product_unit (x y q : R) (a : State R) :
    product x y q ![1,0,0] a = a := by
  funext i
  fin_cases i <;> simp [product]

theorem metric_invariant (x y q : R) (a b c : State R) :
    metric x y (product x y q a b) c = metric x y a (product x y q b c) := by
  exact congrFun (product_assoc x y q a b c) 2

/-- Evaluation in the toric point lift at a root of the quantum cubic. -/
def evaluate (x root : R) (a : State R) : R := a 0 + root*a 1 + root*(root+x)*a 2

theorem evaluate_mul (x y q root : R) (h : root * (root + x) * (root + y) = q) (a b : State R) :
    evaluate x root (product x y q a b) = evaluate x root a * evaluate x root b := by
  rw [← h]
  simp [evaluate, product]
  ring

/-- The full three-point tensor from the source, with its last index lowered
using the metric. The comparison retains the polynomial x-2y for three point lifts. -/
theorem line_tensor (x y : R) (i j k : Fin 3) :
    metric x y (line x y (Pi.single i 1) (Pi.single j 1)) (Pi.single k 1) =
      SmallQuantumGeneratorData.plane x y 0 i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp +decide [SmallQuantumGeneratorData.plane, metric, product, line, Matrix.cons_val_two]
  all_goals ring

end Ring

noncomputable section

abbrev pointEquiv := SurfaceReplay.Plane.accepted.equivalence
def classicalRoot : Fin 3 → Coefficient := ![0, -y, -x]

/-- Evaluation at the undeformed roots is exactly the accepted GKM restriction map. -/
theorem restrict_evaluate (a : State Coefficient) (i : Fin 3) :
    pointEquiv a i = evaluate x (classicalRoot i) a := by
  change (SurfaceReplay.Plane.tables.restrictions *ᵥ a) i = _
  rw [SurfaceReplay.Plane.accepted.restrictions_eq]
  fin_cases i <;> simp [SurfaceFrames.Plane.request, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    evaluate, classicalRoot]
  all_goals ring

/-- The constant term is multiplication in the accepted localized fixed-point algebra. -/
theorem classical_product (a b : State Coefficient) :
    pointEquiv (product x y 0 a b) = pointEquiv a * pointEquiv b := by
  funext i
  simp only [Pi.mul_apply, restrict_evaluate]
  apply evaluate_mul
  fin_cases i <;> simp [classicalRoot]

/-- Independent binding of the lowered metric to the accepted state's metric matrix. -/
theorem metric_table (i j : Fin 3) :
    metric x y (Pi.single i 1) (Pi.single j 1) = SurfaceReplay.Plane.tables.metric i j := by
  fin_cases i <;> fin_cases j <;>
    simp +decide [Matrix.cons_val_two, Matrix.cons_val_three, metric, product,
      SurfaceReplay.Plane.tables,
      SurfaceReplay.Plane.values, SurfaceReplay.Plane.numerators, SurfaceReplay.Plane.denominators,
      map_add, map_mul, map_pow, embed_C, embed_X_zero, embed_X_one]
  all_goals ring

/-- A geometric identification of the metric and of the native three-point values
on the basis identifies the line product with the existing GW coefficient operator. -/
theorem gw_line_on_basis {C : StableCurveCohomology Coefficient}
    (Ω : GromovWittenTheory Coefficient (State Coefficient) SurfaceTarget.plane.Curve
      SurfaceTarget.plane.effective C) (G : GenusZeroGeometry C)
    (hmetric : ∀ (a : State Coefficient) k, Ω.pairing.form a (Pi.single k 1) =
      metric x y a (Pi.single k 1))
    (hthree : ∀ i j k : Fin 3, Ω.threePoint G ![1]
      (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single j 1) (fun _ ↦ Pi.single k 1))) =
      SmallQuantumGeneratorData.plane x y 0 i j k) (i j : Fin 3) :
    Ω.smallQuantumProductCoefficient G ![1] (Pi.single i 1) (Pi.single j 1) =
      line x y (Pi.single i 1) (Pi.single j 1) := by
  apply Ω.pairing.toDual.injective
  apply (Pi.basisFun Coefficient (Fin 3)).ext
  intro k
  rw [Pi.basisFun_apply, Ω.pairing.toDual_apply, Ω.pairing.toDual_apply]
  rw [Ω.pairing_smallQuantumProductCoefficient, hthree, hmetric, line_tensor]

end
end AxiomaticGW.GKM.PlaneSmallQuantumProduct
