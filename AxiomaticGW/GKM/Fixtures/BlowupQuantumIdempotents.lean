/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.FirstOrderFixedPoints
public import AxiomaticGW.GKM.Fixtures.SmallQuantumGeneratorComparison
public import AxiomaticGW.GKM.Fixtures.SurfaceReplay
public import AxiomaticGW.GW.SmallQuantumProduct

/-!
# First-order equivariant primitive idempotents of the two blowups

Every primitive full curve class has an independent square-zero coefficient.
A pair contributes the cube of the difference of its two fixed restrictions.
The fiber of F₁ has two distinct fixed representatives. The six pair contributions
are checked against every entry of the original equivariant
three-point report and the certified equivariant restriction matrices.
-/

@[expose] public section
namespace AxiomaticGW.GKM.BlowupQuantumIdempotents
open EquivariantCoefficients FirstOrderFixedPoints StateSpaceCertificate Matrix
open SmallQuantumGeneratorComparison (tensor generator)
noncomputable section

abbrev Index (X : SurfaceTarget) := Fin (X.blowups + 3)
abbrev Direction (X : SurfaceTarget) := Fin (X.blowups + 1)

/-- The bound source tensor, classical localization frame and a checked decomposition
into cubics of restriction differences. -/
structure Presentation (X : SurfaceTarget) where
  request : Request (X.blowups + 3)
  tables : Tables (X.blowups + 3)
  accepted : Accepts request tables
  pairs : Fin 3 → Pair (Index X)
  weights : Direction X → Fin 3 → Coefficient
  cubic_basis : ∀ d i j k, cubic pairs weights d
    (request.restrictions.col i) (request.restrictions.col j) (request.restrictions.col k) =
    tensor x y X d i j k

namespace Presentation
variable {X : SurfaceTarget} (S : Presentation X)

/-- Actual point restrictions of the held surface basis. -/
def basis (i : Index X) : Index X → Coefficient := S.accepted.equivalence (Pi.single i 1)

theorem basis_correct (i : Index X) : S.basis i = S.request.restrictions.col i := by
  change S.tables.restrictions *ᵥ Pi.single i 1 = _
  rw [Matrix.mulVec_single_one, S.accepted.restrictions_eq]

theorem euler_ne (i : Index X) : S.request.euler i ≠ 0 := by
  rw [← S.accepted.euler_eq]
  exact S.accepted.euler_ne_zero i

/-- The fixed scalar product is precisely the classical exchange metric, in the actual
toric basis order and normalization. -/
theorem metric_basis (i j : Index X) :
    pairing S.request.euler (S.basis i) (S.basis j) = S.tables.metric i j := by
  rw [← S.accepted.metric_correct i j, SymmetricPerfectPairing.comap_apply]
  change _ = tracePairing (FixedPointAlgebra.counit S.accepted.eulerUnits) (S.basis i) (S.basis j)
  rw [tracePairing_apply, FixedPointAlgebra.counit_apply]
  simp only [pairing, StateSpaceCertificate.Accepts.eulerUnits, Units.val_inv_eq_inv_val,
    Units.val_mk0, S.accepted.euler_eq, Pi.mul_apply, mul_assoc]

/-- Coefficient of the full primitive class in fixed-point restrictions, before lowering
the third index. -/
def productCoefficient (d : Direction X) (i j : Index X) : Index X → Coefficient :=
  coeff (product S.request.euler S.pairs S.weights (flat (S.basis i)) (flat (S.basis j))) d

theorem source_pairing (d : Direction X) (i j k : Index X) :
    pairing S.request.euler (S.productCoefficient d i j) (S.basis k) = tensor x y X d i j k := by
  rw [productCoefficient, product_pairing _ _ _ S.euler_ne, S.basis_correct, S.basis_correct,
    S.basis_correct, S.cubic_basis]

/-- Transporting the coefficient back to surface basis coordinates agrees with the existing
GW operator under identification of its incoming metric and three-point correlators. -/
theorem gw_coefficient {C : StableCurveCohomology Coefficient}
    (Ω : GromovWittenTheory Coefficient (Index X → Coefficient) X.Curve X.effective C)
    (G : GenusZeroGeometry C)
    (hmetric : ∀ a k, Ω.pairing.form a (Pi.single k 1) =
      pairing S.request.euler (S.accepted.equivalence a) (S.basis k))
    (hthree : ∀ d i j k, Ω.threePoint G (generator X d)
      (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single j 1) (fun _ ↦ Pi.single k 1))) =
      tensor x y X d i j k) (d : Direction X) (i j : Index X) :
    Ω.smallQuantumProductCoefficient G (generator X d) (Pi.single i 1) (Pi.single j 1) =
      S.accepted.equivalence.symm (S.productCoefficient d i j) := by
  apply Ω.pairing.toDual.injective
  apply (Pi.basisFun Coefficient (Index X)).ext
  intro k
  rw [Pi.basisFun_apply, Ω.pairing.toDual_apply, Ω.pairing.toDual_apply,
    Ω.pairing_smallQuantumProductCoefficient, hthree, hmetric,
    S.accepted.equivalence.apply_symm_apply, S.source_pairing]

/-- The exact Gram matrix of the lifted primitive basis. -/
theorem projector_metric (i j : Index X) :
    metric S.request.euler (projector S.request.euler S.pairs S.weights i)
      (projector S.request.euler S.pairs S.weights j) =
      if i = j then norm S.request.euler S.pairs S.weights i else 0 := by
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, projector_norm]
  · rw [if_neg h, metric_orthogonal _ _ _ S.euler_ne i j h]

/-- Inverse Gram matrix used for edge contractions in the unnormalized primitive basis. -/
def inverseGram : Matrix (Index X) (Index X) (Scalars Coefficient (Direction X)) :=
  diagonal (inverseNorm S.request.euler S.pairs S.weights)

def gram : Matrix (Index X) (Index X) (Scalars Coefficient (Direction X)) :=
  fun i j ↦ metric S.request.euler (projector S.request.euler S.pairs S.weights i)
    (projector S.request.euler S.pairs S.weights j)

theorem gram_mul_inverse : S.gram * S.inverseGram = 1 := by
  have hg : S.gram = diagonal (norm S.request.euler S.pairs S.weights) := by
    funext i j
    rw [gram, S.projector_metric, diagonal_apply]
  rw [hg, inverseGram, diagonal_mul_diagonal]
  simp only [norm_mul_inverseNorm _ _ _ S.euler_ne, diagonal_one]

/-- The degree-one loop symplecticity test in this primitive frame uses the actual
first-order norms. The matrix B is supplied by a separate calibration. -/
theorem selfAdjoint_iff (B : Matrix (Index X) (Index X) (Scalars Coefficient (Direction X))) :
    diagonal (norm S.request.euler S.pairs S.weights) * B =
      B.transpose * diagonal (norm S.request.euler S.pairs S.weights) ↔
    ∀ i j, norm S.request.euler S.pairs S.weights i * B i j =
      B j i * norm S.request.euler S.pairs S.weights j := by
  constructor
  · intro h i j
    simpa only [diagonal_mul, mul_diagonal, transpose_apply] using congrFun (congrFun h i) j
  · intro h
    funext i j
    simpa only [diagonal_mul, mul_diagonal, transpose_apply] using h i j

/-- After extending the actual incoming character field, choose signs for the
Euler square roots and normalize the complete Gram diagonal. -/
theorem normalized_over {L : Type*} [Field L] [IsAlgClosed L] (f : Coefficient →+* L) :
    ∃ s : Index X → L, ∀ i, (s i)^2 = f (S.request.euler i) ∧
      mapScalar f (norm S.request.euler S.pairs S.weights i) *
        normalizer (f ∘ S.request.euler) S.pairs
          (fun g t ↦ f (S.weights g t)) i (s i)^2 = 1 := by
  simp only [map_norm]
  exact exists_normalized_gram _ _ _ (fun i ↦ (map_ne_zero f).mpr (S.euler_ne i))

end Presentation

namespace OneBlowup

def pairs : Fin 3 → Pair (Fin 4) := ![⟨1,3⟩,⟨0,1⟩,⟨2,3⟩]

/-- Cubic coefficients in the fixed-point frame, in primitive curve order. -/
def weights : Fin 2 → Fin 3 → Coefficient :=
  !![-1 / (x-y)^3, 0, 0; 0, 1 / (y^3*(x-y)), -1 / (x^3*(x-y))]

private def scale : Fin 3 → Coefficient := ![x-y,y,x]
private def covector : Matrix (Fin 3) (Fin 4) Coefficient := !![0,0,1,0; 0,1,1,x-y; 0,1,1,0]
private def factor : Matrix (Fin 2) (Fin 3) Coefficient := !![-1,0,0; 0,(x-y)⁻¹,-(x-y)⁻¹]

private theorem difference (t : Fin 3) (i : Fin 4) :
    (pairs t).diff (SurfaceFrames.OneBlowup.request.restrictions.col i) =
      scale t * covector t i := by
  fin_cases t <;> fin_cases i <;>
    simp +decide [pairs, Pair.diff, SurfaceFrames.OneBlowup.request, scale, covector,
      Matrix.col, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem factor_correct (d : Fin 2) (t : Fin 3) :
    weights d t * scale t ^ 3 = factor d t := by
  fin_cases d <;> fin_cases t <;>
    simp +decide [weights, scale, factor, Matrix.cons_val_two] <;>
    field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero]

private def term (i j k : Fin 4) (t : Fin 3) : Coefficient :=
  covector t i * covector t j * covector t k

set_option maxHeartbeats 6000000 in
-- Enumerate all ordered marked states and simplify the exact character-field coefficients.
private theorem source (d : Fin 2) (i j k : Fin 4) :
    (∑ t, factor d t * term i j k t) =
      SmallQuantumGeneratorData.one x y d i j k := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp +decide [Fin.sum_univ_three, factor, term, covector,
      SmallQuantumGeneratorData.one, Matrix.cons_val_two, Matrix.cons_val_three,
      x_sub_y_ne_zero] <;> field_simp [x_sub_y_ne_zero] <;> ring

def presentation : Presentation .hirzebruchOne where
  request := SurfaceFrames.OneBlowup.request
  tables := SurfaceReplay.OneBlowup.tables
  accepted := SurfaceReplay.OneBlowup.accepted
  pairs := pairs
  weights := weights
  cubic_basis d i j k := by
    change cubic pairs weights d (SurfaceFrames.OneBlowup.request.restrictions.col i)
      (SurfaceFrames.OneBlowup.request.restrictions.col j)
      (SurfaceFrames.OneBlowup.request.restrictions.col k) =
      SmallQuantumGeneratorData.one x y d i j k
    unfold cubic
    rw [← source]
    apply Finset.sum_congr rfl
    intro t _
    rw [difference, difference, difference, ← factor_correct]
    dsimp [term]
    ring

end OneBlowup

namespace TwoBlowups

def pairs : Fin 3 → Pair (Fin 5) := ![⟨1,2⟩,⟨3,4⟩,⟨2,3⟩]

/-- Cubic coefficients in the fixed-point frame, in primitive curve order. -/
def weights : Fin 3 → Fin 3 → Coefficient :=
  !![-1 / (x-y)^3, 0, 0; 0, -1/y^3, 0; 0, 0, -1/x^3]

private def scale : Fin 3 → Coefficient := ![x-y,y,-x]
private def covector : Matrix (Fin 3) (Fin 5) Coefficient := !![0,0,1,0,0; 0,0,0,1,0; 0,1,1,1,0]
private def factor : Matrix (Fin 3) (Fin 3) Coefficient := !![-1,0,0; 0,-1,0; 0,0,1]

private theorem difference (t : Fin 3) (i : Fin 5) :
    (pairs t).diff (SurfaceFrames.TwoBlowups.request.restrictions.col i) =
      scale t * covector t i := by
  fin_cases t <;> fin_cases i <;>
    simp +decide [pairs, Pair.diff, SurfaceFrames.TwoBlowups.request, scale, covector,
      Matrix.col, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem factor_correct (d : Fin 3) (t : Fin 3) :
    weights d t * scale t ^ 3 = factor d t := by
  fin_cases d <;> fin_cases t <;>
    simp +decide [weights, scale, factor, Matrix.cons_val_two] <;>
    field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero]

private def term (i j k : Fin 5) (t : Fin 3) : Coefficient :=
  covector t i * covector t j * covector t k

set_option maxHeartbeats 6000000 in
-- Enumerate all ordered marked states and simplify the exact character-field coefficients.
private theorem source (d : Fin 3) (i j k : Fin 5) :
    (∑ t, factor d t * term i j k t) =
      SmallQuantumGeneratorData.two x y d i j k := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp +decide [Fin.sum_univ_three, factor, term, covector,
      SmallQuantumGeneratorData.two, Matrix.cons_val_two, Matrix.cons_val_three]

def presentation : Presentation .blowupTwo where
  request := SurfaceFrames.TwoBlowups.request
  tables := SurfaceReplay.TwoBlowups.tables
  accepted := SurfaceReplay.TwoBlowups.accepted
  pairs := pairs
  weights := weights
  cubic_basis d i j k := by
    change cubic pairs weights d (SurfaceFrames.TwoBlowups.request.restrictions.col i)
      (SurfaceFrames.TwoBlowups.request.restrictions.col j)
      (SurfaceFrames.TwoBlowups.request.restrictions.col k) =
      SmallQuantumGeneratorData.two x y d i j k
    unfold cubic
    rw [← source]
    apply Finset.sum_congr rfl
    intro t _
    rw [difference, difference, difference, ← factor_correct]
    dsimp [term]
    ring

end TwoBlowups

end
end AxiomaticGW.GKM.BlowupQuantumIdempotents
