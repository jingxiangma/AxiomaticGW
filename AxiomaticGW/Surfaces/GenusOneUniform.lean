/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusOneMarkings

/-!
# A uniform genus-one Getzler pivot

At energy at least two, four original hyperplanes and `energy - 2` additional
points give elliptic coefficient minus nine. Only the three labelled two-tail graphs contribute:
each rational three-point tail contracts two hyperplanes to a point on the
elliptic component. Other tree types vanish by classical arity or dimension;
loop types have no elliptic vertex. The coefficient comparison retains the
original 33 columns and every ordered marking placement.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusOne

open SurfacePolynomialReduction

private theorem rational_constant {X : SurfaceTarget} (S : Type) [Fintype S]
    (h : StableArity 0 S) (a : S → SurfaceBasisLabel X) :
    constantCoefficient (GluingExpression.fundamental 0 S h) a =
      if ((∑ s, (a s).codimension : ℕ) : ℤ) = -1 + (Fintype.card S : ℤ) then
        if Fintype.card S = 3 then
          SurfaceCohomology.counit X.blowups (∏ s, (a s).value) else 0
      else 0 := by
  change SurfaceGenusZero.constantCoefficient _ _ = _
  rw [SurfaceGenusZero.constantCoefficient_fundamental]
  simp only [SurfaceAncestorKey.DimensionCompatible, SurfaceAncestorKey.totalCodimension,
    SurfaceAncestorKey.primaryLabels, SurfaceAncestorKey.ofLabels, SurfacePrimary.classicalValue,
    Multiset.map_map, Function.comp_def, Pi.zero_apply, add_zero, Nat.cast_zero,
    map_zero, zero_sub, Multiset.card_map, Finset.card_val, Finset.card_univ]
  rfl

private theorem shifted_delta22 (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.delta22Expression (by omega)
      (fun _ ↦ .hyperplane) =
      pointVertexCoefficient X beta n (fun _ : Fin 2 ↦ .point) := by
  have hf (i : Fin 2) : finSuccEquiv 2 (Fin.natAdd 1 i) = some i := by
    fin_cases i <;> rfl
  simp only [GetzlerGraphs.delta22Expression, GetzlerGraphs.join, shiftedPointCoefficient,
    Nat.zero_ne_one, ite_false, ite_true, mul_zero, zero_add,
    constantCoefficient_relabel, rational_constant, SurfaceBasisLabel.sum_labels]
  -- The finite flag maps and cubic intersection are checked directly.
  norm_num [Function.comp_def, finSuccEquiv'_zero, hf, Fin.sum_univ_succ, Fin.prod_univ_succ,
    SurfaceBasisLabel.codimension, SurfaceBasisLabel.value,
    SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    pow_two,
    SurfaceCohomology.hyperplane_mul_hyperplane, SurfaceCohomology.counit_point]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem shifted_delta23 (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.delta23Expression (by omega)
      (fun _ ↦ .hyperplane) = 0 := by
  have hf (i : Fin 2) : finSuccEquiv' (2 : Fin 3) (Fin.natAdd 1 i) =
      if i = 0 then some 1 else none := by
    fin_cases i <;> rfl
  simp only [GetzlerGraphs.delta23Expression, GetzlerGraphs.join, shiftedPointCoefficient,
    Nat.zero_ne_one, ite_false, ite_true, mul_zero, zero_add,
    constantCoefficient_relabel, rational_constant, SurfaceBasisLabel.sum_labels]
  -- The finite flag maps and cubic intersection are checked directly.
  norm_num [Function.comp_def, finSuccEquiv'_zero, hf, Fin.sum_univ_succ, Fin.prod_univ_succ,
    SurfaceBasisLabel.codimension, SurfaceBasisLabel.value,
    SurfaceBasisLabel.inverseWeight, SurfaceBasisLabel.dual,
    pow_two, SurfaceCohomology.hyperplane_mul_hyperplane, SurfaceCohomology.counit_point]

private theorem shifted_delta24 (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.delta24Expression (by omega)
      (fun _ ↦ .hyperplane) = 0 := by
  simp only [GetzlerGraphs.delta24Expression, GetzlerGraphs.join, shiftedPointCoefficient,
    Nat.zero_ne_one, ite_false, ite_true, mul_zero, zero_add,
    constantCoefficient_relabel, rational_constant, SurfaceBasisLabel.sum_labels]
  -- A rational vertex has four flags, so its class-zero primary value vanishes.
  norm_num

private theorem shifted_delta34 (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.delta34Expression (by omega)
      (fun _ ↦ .hyperplane) = 0 := by
  simp only [GetzlerGraphs.delta34Expression, GetzlerGraphs.join, shiftedPointCoefficient,
    Nat.zero_ne_one, ite_false, ite_true, mul_zero, zero_add,
    constantCoefficient_relabel, rational_constant, SurfaceBasisLabel.sum_labels]
  -- A rational vertex has four flags, so its class-zero primary value vanishes.
  norm_num

private theorem shifted_delta03 (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.delta03Expression (by omega)
      (fun _ ↦ .hyperplane) = 0 := by
  simp only [GetzlerGraphs.delta03Expression, GetzlerGraphs.join, GetzlerGraphs.close,
    shiftedPointCoefficient, Nat.zero_ne_one, ite_false, mul_zero, zero_mul,
    zero_add, Finset.sum_const_zero]

private theorem shifted_delta04 (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.delta04Expression (by omega)
      (fun _ ↦ .hyperplane) = 0 := by
  simp only [GetzlerGraphs.delta04Expression, GetzlerGraphs.join, GetzlerGraphs.close,
    shiftedPointCoefficient, Nat.zero_ne_one, ite_false, mul_zero, zero_mul,
    zero_add, Finset.sum_const_zero]

private theorem shifted_deltaBeta (X : SurfaceTarget) (beta : X.Curve) (n : ℕ) :
    shiftedPointCoefficient X beta n GetzlerGraphs.deltaBetaExpression (by omega)
      (fun _ ↦ .hyperplane) = 0 := by
  rfl

end AxiomaticGW.SurfaceGenusOne

namespace AxiomaticGW.GetzlerGraphs

open SurfaceGenusOne

/-- Four hyperplanes at the original markings. -/
def reconstructionLabels (X : SurfaceTarget) : Fin 4 → SurfaceBasisLabel X :=
  fun _ ↦ .hyperplane

private theorem shifted_representative (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    (s : GetzlerStratum) :
    shiftedPointCoefficient X beta n (representativeExpression s) (by omega)
      (reconstructionLabels X) =
        if s = .delta22 then pointVertexCoefficient X beta n (fun _ : Fin 2 ↦ .point)
        else 0 := by
  cases s <;> simp only [representativeExpression, reduceCtorEq, ite_true, ite_false]
  · exact shifted_delta22 X beta n
  · exact shifted_delta23 X beta n
  · exact shifted_delta24 X beta n
  · exact shifted_delta34 X beta n
  · exact shifted_delta03 X beta n
  · exact shifted_delta04 X beta n
  · exact shifted_deltaBeta X beta n

private theorem delta22_weight :
    (∑ i : Fin 33, if kind i = .delta22 then requested i else 0) = (-9 : ℚ) := by
  decide +kernel

/-- The original four-hyperplane family has a uniform elliptic coefficient. -/
theorem pointMarkedCoefficient_reconstruction (X : SurfaceTarget) (n : ℕ) (beta : X.Curve)
    (henergy : X.effective.energy beta = n + 2) :
    pointMarkedCoefficient X n beta (reconstructionLabels X) = -9 := by
  have hp : pointVertexCoefficient X beta n (fun _ : Fin 2 ↦ .point) = 1 := by
    unfold pointVertexCoefficient
    have hd : ((∑ _ : Fin 2, SurfaceBasisLabel.codimension
          (SurfaceBasisLabel.point : SurfaceBasisLabel X) : ℕ) : ℤ) + (n : ℤ) =
        X.c1Degree beta + (Fintype.card (Fin 2) : ℤ) := by
      change (4 : ℤ) + (n : ℤ) = (X.effective.energy beta : ℤ) + 2
      rw [henergy]
      omega
    rw [if_pos hd]
    simp only [SurfaceBasisLabel.primaryFactor, Finset.prod_const_one]
  have hi (i : Fin 33) : shiftedPointCoefficient X beta n (expression i) (by omega)
      (reconstructionLabels X) = if kind i = .delta22 then 1 else 0 := by
    change shiftedPointCoefficient X beta n (representativeExpression (kind i)) (by omega)
      (reconstructionLabels X) = _
    rw [shifted_representative, hp]
  simp only [pointMarkedCoefficient, hi, mul_ite, mul_one, mul_zero]
  exact delta22_weight

/-- The coefficient is computed in the complete original marking-placement polynomial. -/
theorem primaryTerms_reconstruction_coefficient (X : SurfaceTarget) (beta : X.Curve)
    (henergy : 2 ≤ X.effective.energy beta) :
    RationalTerms.coefficient
      (primaryTerms X (X.effective.energy beta - 2) beta 0
        (SurfaceGenusZero.pointLabels (reconstructionLabels X) (X.effective.energy beta - 2)))
      {SurfaceLowGenus.pointVariable X 1 beta} = -9 := by
  have hbeta : beta ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at henergy
    omega
  rw [← pointMarkedCoefficient_eq X _ beta hbeta]
  exact pointMarkedCoefficient_reconstruction X _ beta (Nat.sub_add_cancel henergy).symm

end AxiomaticGW.GetzlerGraphs
