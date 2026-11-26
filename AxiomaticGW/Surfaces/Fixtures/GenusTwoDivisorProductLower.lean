/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoTwoMarkingProduct
public import AxiomaticGW.Surfaces.GenusTwoL24PointCache
public import AxiomaticGW.Surfaces.PointBenchmarkCache
public import AxiomaticGW.Surfaces.ScalarAncestorStep
public import AxiomaticGW.Surfaces.ZeroPointContraction

/-! # The 24 lower-genus graphs of the primitive two-divisor product

The effective-coordinate contraction includes the original node powers,
curve splittings and inverse metric. Each original graph is checked across
the entire finite degree-one divisor frame.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoDivisorProductLower
open SurfaceGenusTwo SurfacePointBenchmarkCache GenusTwoPsiProduct
variable {X : SurfaceTarget}

/-- Dimension-guarded lower-genus terminal with the certified primary caches. -/
def lower (X : SurfaceTarget) : SurfaceCotangentVertexValues X ℚ := fun g S _ h d _ beta a ↦
  if g ≤ 1 then
    let q := SurfaceAncestorKey.ofLabels g S h beta d a
    if q.DimensionCompatible then
      SurfaceLowGenusPointCache.scalarComponentValue X (genusZero X) (genusOne X) q
    else 0
  else 0

private theorem lower_eq (X : SurfaceTarget) : lower X =
    SurfacePointPullback.vertex X (constantVertexWithPoints X (genusZero X) (genusOne X)) 0 := by
  funext g S inst h d l beta a
  simp only [lower, SurfacePointPullback.vertex, constantVertexWithPoints,
    SurfaceLowGenusPointCache.scalarComponentValue_eq]

/-- The successor index omits precisely the unique genus-two graph. -/
def weighted (beta : X.Curve) (a b : SurfaceBasisLabel X) (i : Fin 24) : ℚ :=
  let z := boundaryCotangentTerm i.succ
  boundary (boundaryIndex i.succ) * z.expression.zeroPointContraction X (lower X)
    z.decoration z.labels beta ![a, b]

theorem weighted_eq (v : SurfaceAncestorKey X → ℚ) (beta : X.Curve) (a b : SurfaceBasisLabel X)
    (i : Fin 24) : weighted beta a b i = productGraph (productVertex v) beta ![a, b] i.succ := by
  simp only [weighted, lower_eq, GluingExpression.zeroPointContraction_eq,
    SurfacePointPullback.contraction_zero, constantVertexWithPoints_eq X _ _ (genusZero_eq X)
      (genusOne_eq X)]
  apply congrArg (boundary (boundaryIndex i.succ) * ·)
  apply GluingExpression.surfaceDecoratedEval_congr_of_genus
  intro g S _ h gamma k labels hg
  have hlow := hg.trans (boundaryTerm_lower_genus i.succ (Fin.succ_ne_zero i))
  unfold constantVertex productVertex vertexTerms residualTerms
  simp only [SurfaceAncestorKey.ofLabels, hlow, if_true]
  split_ifs <;> simp only [RationalTerms.eval_term, RationalTerms.eval_zero,
    Algebra.algebraMap_self_apply, Multiset.map_zero, Multiset.prod_zero, mul_one]

/-- Signed graph values at unit divisor pairings, in the original source order. -/
def row : Fin 24 → ℚ :=
  ![-161/25920, -161/25920, 5/324, 0, 0, 0, 0, 0, 0, 0, 13/17280, 0,
    7/432, -67/8640, -67/8640, 0, 0, 0, 0, 0, 0, 0, 37/17280, 1/720]

set_option Elab.async false
set_option maxRecDepth 65536

private def rowAt (X : SurfaceTarget) (i : Fin 24) : Prop :=
  ∀ beta ∈ X.bounded 1, X.effective.energy beta = 1 →
    ∀ a b : SurfaceBasisLabel X, a.codimension = 1 → b.codimension = 1 →
      weighted beta a b i = row i * (a.primaryFactor beta * b.primaryFactor beta)

private instance (X : SurfaceTarget) (i : Fin 24) : Decidable (rowAt X i) := by
  unfold rowAt
  infer_instance

private def blockIndex (j : Fin 4) (k : Fin 6) : Fin 24 := ⟨6 * j.val + k.val, by omega⟩

private def block (j : Fin 4) := ∀ (X : SurfaceTarget) (k : Fin 6), rowAt X (blockIndex j k)

set_option maxHeartbeats 2400000 in
-- Six source graphs, each checked at every degree-one class and ordered divisor pair.
private theorem block0 : block 0 := by
  intro X k
  cases X <;> fin_cases k <;> decide +kernel

set_option maxHeartbeats 2400000 in
-- Six source graphs, each checked at every degree-one class and ordered divisor pair.
private theorem block1 : block 1 := by
  intro X k
  cases X <;> fin_cases k <;> decide +kernel

set_option maxHeartbeats 2400000 in
-- Six source graphs, each checked at every degree-one class and ordered divisor pair.
private theorem block2 : block 2 := by
  intro X k
  cases X <;> fin_cases k <;> decide +kernel

set_option maxHeartbeats 2400000 in
-- Six source graphs, each checked at every degree-one class and ordered divisor pair.
private theorem block3 : block 3 := by
  intro X k
  cases X <;> fin_cases k <;> decide +kernel

private theorem checkRow (X : SurfaceTarget) (i : Fin 24) : rowAt X i := by
  let b : Fin 4 := ⟨i.val / 6, by omega⟩
  let k : Fin 6 := ⟨i.val % 6, by omega⟩
  have h (j : Fin 4) : block j := by
    fin_cases j
    · exact block0
    · exact block1
    · exact block2
    · exact block3
  have hi : blockIndex b k = i := by
    apply Fin.ext
    change 6 * (i.val / 6) + i.val % 6 = i.val
    omega
  rw [← hi]
  exact h b X k

/-- Exact total lower-genus contribution at every full anticanonical degree-one class. -/
theorem sum_eq (v : SurfaceAncestorKey X → ℚ) (beta : X.Curve) (he : X.effective.energy beta = 1)
    (a b : SurfaceBasisLabel X) (ha : a.codimension = 1) (hb : b.codimension = 1) :
    (∑ i : Fin 24, productGraph (productVertex v) beta ![a, b] i.succ) =
      23/2880 * (a.primaryFactor beta * b.primaryFactor beta) := by
  have hc (i : Fin 24) := checkRow X i beta (by rw [X.bounded_eq, X.effective.mem_bounded, he])
    he a b ha hb
  simp only [← weighted_eq, hc, ← Finset.sum_mul]
  rw [show (∑ i, row i) = 23/2880 by decide +kernel]

end AxiomaticGW.SurfaceGenusTwoDivisorProductLower
