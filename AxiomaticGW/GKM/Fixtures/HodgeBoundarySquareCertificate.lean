/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.HodgeBoundarySquareRows
public import AxiomaticGW.GKM.Fixtures.HodgeLoopSquare
public import AxiomaticGW.GKM.Fixtures.HodgeLoopSeparatingProduct
public import AxiomaticGW.GKM.Fixtures.HodgeSeparatingSquare

/-!
# Degree-two replay on the held Hodge and boundary packets

Each source occurrence is identified with a decorated graph in the external
seventeen-column frame. The certificate compares the actual sixteen-term
packet with the loop, mixed and separating parts of the held product.
-/

@[expose] public section
namespace AxiomaticGW.GKM.HodgeBoundarySquareCertificate
open RelationCertificate AdmcyclesHodgeStrataCandidates HodgeBoundarySquareRows

/-- Every source (0,2) occurrence has the specified decorated-graph meaning. -/
theorem half_columns (i : Fin 16) : raw02Degree2Columns i = columns (halfIndices i) := by
  fin_cases i <;> first
    | rfl
    | apply TautologicalStratum.mk_eq_mk_of_isomorphic?
      simp only [DecoratedStableGraph.toDecoration_eq_mk]
      decide +kernel

/-- Both branches and all decorations are preserved for each of the 28 product occurrences. -/
theorem square_columns (i : Fin 28) : raw11Degree2Columns i = columns (squareIndices i) := by
  fin_cases i <;> first
    | rfl
    | apply TautologicalStratum.mk_eq_mk_of_isomorphic?
      simp only [DecoratedStableGraph.toDecoration_eq_mk]
      decide +kernel

/-- The independent half-square vector denotes the complete held (0,2) expression. -/
theorem interpret_half : interpret columns half = raw02Degree2 := by
  have he : (∑ j, Pi.single (halfIndices j) (raw02Degree2Coordinates j)) = half := by
    funext i
    revert i
    decide +kernel
  rw [← he]
  exact (AdmcyclesHodgeStrataIsomorphisms.interpret_grouped _ _ _ _ half_columns).symm

/-- Multiply the marked loop, mixed and separating graph contributions by the coefficients
that convert the original Hodge square to the discriminant square. -/
noncomputable def squarePacket : StrataModule 2 (Fin 1) :=
  (144 : ℚ) • LoopSquarePacketBinding.packetPart +
  (288 : ℚ) • HodgeLoopSeparatingProduct.packetPart +
  (576 : ℚ) • HodgeSeparatingSquare.packetPart

private def term (i : Fin 28) : Coordinates 17 :=
  Pi.single (squareIndices i) (raw11Degree2Coordinates i)

private theorem interpret_term (i : Fin 28) :
    interpret columns (term i) =
      raw11Degree2Coordinates i • StrataModule.basis (raw11Degree2Columns i) := by
  rw [interpret_apply, square_columns]
  simp only [term, Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

private def boundaryTerms : Coordinates 17 :=
  (144 : ℚ) • (term 3 + term 4 + term 18 + term 21 + term 23) +
  (288 : ℚ) • (term 17 + term 22 + term 24 + term 25 + term 26 + term 27) +
  (576 : ℚ) • (term 5 + term 6 + term 7 + term 8 + term 19 + term 20)

/-- The independent source boundary product retains the actual shared-edge excess terms. -/
theorem interpret_boundarySquare : interpret columns boundarySquare = squarePacket := by
  have he : boundaryTerms = boundarySquare := by funext i; revert i; decide +kernel
  rw [← he]
  simp only [boundaryTerms, map_add, map_smul, interpret_term]
  rfl

/-- The checked original rows have exactly the desired residual in the free strata module. -/
theorem interpret_residual : interpret columns residual =
    (200 : ℚ) • raw02Degree2 - squarePacket := by
  have he : residual = (200 : ℚ) • half - boundarySquare := by
    funext i
    revert i
    decide +kernel
  rw [he, map_sub, map_smul, interpret_half, interpret_boundarySquare]

/-- In the quotient by the original rows the held (0,2) packet equals 1/200 of the
discriminant square, with the original excess corrections. -/
theorem quotient_half :
    let proj := StrataModule.quotientMk (relationSpan columns rows)
    proj raw02Degree2 = (1 / 200 : ℚ) • proj squarePacket := by
  have h := quotient_eq_zero columns rows residual witness checked
  rw [interpret_residual, map_sub, map_smul, sub_eq_zero] at h
  dsimp only
  rw [← h, smul_smul]
  norm_num

/-- The full six interior/eight boundary frame is retained. Exactly its first twelve
original generators enter the held witness with nonzero weight. -/
theorem witness_support (i : Fin 14) : witness.weights i ≠ 0 ↔ i.val < 12 := by
  revert i
  decide +kernel

/-- Vanishing is needed only for the original rows that contribute to the checked witness. -/
theorem map_half {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ev : StrataModule 2 (Fin 1) →ₗ[ℚ] V)
    (hrows : ∀ i, witness.weights i ≠ 0 → ev (interpret columns (rows i)) = 0) :
    ev raw02Degree2 = (1 / 200 : ℚ) • ev squarePacket := by
  have h : ev (interpret columns residual) = 0 := by
    rw [← (check_eq_true_iff rows residual witness).mp checked, interpret_combination, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    by_cases hw : witness.weights i = 0
    · rw [hw, zero_smul]
    · rw [hrows i hw, smul_zero]
  rw [interpret_residual, map_sub, map_smul, sub_eq_zero] at h
  rw [← h, smul_smul]
  norm_num

end AxiomaticGW.GKM.HodgeBoundarySquareCertificate
