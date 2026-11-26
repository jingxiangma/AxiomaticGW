/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.L24

/-!
# A complete L24 surface coefficient check

Every held column is replayed separately before the full equation is collected.
The degree-zero plane example reproduces a residual genus-two dilaton equation;
it is a normalization regression, not a new invariant value or seed.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceL24
open GluingExpression

set_option Elab.async false
set_option maxRecDepth 20000

/-- Collected equation for the four original states `H,H,1,1` in class zero. -/
def planeZero : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.term 1 {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩} +
  RationalTerms.term (-3) {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩}

private def planeZeroColumn (i : Fin 815) : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.scale (L24CorrectionsReplay.fullClaim i)
    ((L24Gluing.term i).expression.surfaceDecoratedTerms .plane
      (SurfaceGenusTwo.vertexTerms .plane) (L24Gluing.term i).decoration 0 0
      ![.hyperplane, .hyperplane, .unit, .unit])

/-- Held uncollected contributions; zero columns and cancelling terms stay in the check. -/
private def planeZeroExpanded (i : Fin 815) : RationalTerms (SurfaceAncestorKey .plane) :=
  if i.val = 51 then
    {(1/3, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 52 then
    {(-1/1, {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 57 then
    {(1/2, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 59 then
    {(1/2, {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 62 then
    {(-1/1, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 64 then
    {(1/2, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 66 then
    {(1/2, {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 69 then
    {(-1/1, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 76 then
    {(1/3, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 83 then
    {(1/3, {⟨2, ![0], {⟨.hyperplane, 0⟩, ⟨.hyperplane, 1⟩}, by decide +kernel⟩})} else
  if i.val = 93 then
    {(1/2, {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 95 then
    {(1/2, {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 109 then
    {(-1/2, {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 110 then
    {(-1/2, {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 112 then
    {(-1/2, {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 113 then
    {(-1/2, {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 119 then
    {(-1/2, {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩})} else
  if i.val = 120 then
    {(-1/2, {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩})} else
  0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block0 : ∀ i : Fin 815,
    0 ≤ i.val → i.val < 32 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block1 : ∀ i : Fin 815,
    32 ≤ i.val → i.val < 64 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block2 : ∀ i : Fin 815,
    64 ≤ i.val → i.val < 96 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block3 : ∀ i : Fin 815,
    96 ≤ i.val → i.val < 128 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block4 : ∀ i : Fin 815,
    128 ≤ i.val → i.val < 160 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block5 : ∀ i : Fin 815,
    160 ≤ i.val → i.val < 192 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block6 : ∀ i : Fin 815,
    192 ≤ i.val → i.val < 224 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block7 : ∀ i : Fin 815,
    224 ≤ i.val → i.val < 256 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block8 : ∀ i : Fin 815,
    256 ≤ i.val → i.val < 288 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block9 : ∀ i : Fin 815,
    288 ≤ i.val → i.val < 320 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block10 : ∀ i : Fin 815,
    320 ≤ i.val → i.val < 352 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block11 : ∀ i : Fin 815,
    352 ≤ i.val → i.val < 384 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block12 : ∀ i : Fin 815,
    384 ≤ i.val → i.val < 416 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block13 : ∀ i : Fin 815,
    416 ≤ i.val → i.val < 448 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block14 : ∀ i : Fin 815,
    448 ≤ i.val → i.val < 480 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block15 : ∀ i : Fin 815,
    480 ≤ i.val → i.val < 512 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block16 : ∀ i : Fin 815,
    512 ≤ i.val → i.val < 544 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block17 : ∀ i : Fin 815,
    544 ≤ i.val → i.val < 576 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block18 : ∀ i : Fin 815,
    576 ≤ i.val → i.val < 608 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block19 : ∀ i : Fin 815,
    608 ≤ i.val → i.val < 640 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block20 : ∀ i : Fin 815,
    640 ≤ i.val → i.val < 672 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block21 : ∀ i : Fin 815,
    672 ≤ i.val → i.val < 704 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block22 : ∀ i : Fin 815,
    704 ≤ i.val → i.val < 736 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block23 : ∀ i : Fin 815,
    736 ≤ i.val → i.val < 768 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block24 : ∀ i : Fin 815,
    768 ≤ i.val → i.val < 800 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block25 : ∀ i : Fin 815,
    800 ≤ i.val → i.val < 815 → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

private theorem planeZero_columns_checked (i : Fin 815) :
    planeZeroColumn i = planeZeroExpanded i := by
  by_cases h0 : i.val < 32
  · exact planeZero_block0 i (Nat.zero_le _) h0
  by_cases h1 : i.val < 64
  · exact planeZero_block1 i (Nat.le_of_not_gt h0) h1
  by_cases h2 : i.val < 96
  · exact planeZero_block2 i (Nat.le_of_not_gt h1) h2
  by_cases h3 : i.val < 128
  · exact planeZero_block3 i (Nat.le_of_not_gt h2) h3
  by_cases h4 : i.val < 160
  · exact planeZero_block4 i (Nat.le_of_not_gt h3) h4
  by_cases h5 : i.val < 192
  · exact planeZero_block5 i (Nat.le_of_not_gt h4) h5
  by_cases h6 : i.val < 224
  · exact planeZero_block6 i (Nat.le_of_not_gt h5) h6
  by_cases h7 : i.val < 256
  · exact planeZero_block7 i (Nat.le_of_not_gt h6) h7
  by_cases h8 : i.val < 288
  · exact planeZero_block8 i (Nat.le_of_not_gt h7) h8
  by_cases h9 : i.val < 320
  · exact planeZero_block9 i (Nat.le_of_not_gt h8) h9
  by_cases h10 : i.val < 352
  · exact planeZero_block10 i (Nat.le_of_not_gt h9) h10
  by_cases h11 : i.val < 384
  · exact planeZero_block11 i (Nat.le_of_not_gt h10) h11
  by_cases h12 : i.val < 416
  · exact planeZero_block12 i (Nat.le_of_not_gt h11) h12
  by_cases h13 : i.val < 448
  · exact planeZero_block13 i (Nat.le_of_not_gt h12) h13
  by_cases h14 : i.val < 480
  · exact planeZero_block14 i (Nat.le_of_not_gt h13) h14
  by_cases h15 : i.val < 512
  · exact planeZero_block15 i (Nat.le_of_not_gt h14) h15
  by_cases h16 : i.val < 544
  · exact planeZero_block16 i (Nat.le_of_not_gt h15) h16
  by_cases h17 : i.val < 576
  · exact planeZero_block17 i (Nat.le_of_not_gt h16) h17
  by_cases h18 : i.val < 608
  · exact planeZero_block18 i (Nat.le_of_not_gt h17) h18
  by_cases h19 : i.val < 640
  · exact planeZero_block19 i (Nat.le_of_not_gt h18) h19
  by_cases h20 : i.val < 672
  · exact planeZero_block20 i (Nat.le_of_not_gt h19) h20
  by_cases h21 : i.val < 704
  · exact planeZero_block21 i (Nat.le_of_not_gt h20) h21
  by_cases h22 : i.val < 736
  · exact planeZero_block22 i (Nat.le_of_not_gt h21) h22
  by_cases h23 : i.val < 768
  · exact planeZero_block23 i (Nat.le_of_not_gt h22) h23
  by_cases h24 : i.val < 800
  · exact planeZero_block24 i (Nat.le_of_not_gt h23) h24
  exact planeZero_block25 i (Nat.le_of_not_gt h24) i.isLt

private theorem planeZero_expanded_checked :
    L24Relation.genusTwoTerms .plane 0 0 0 ![.hyperplane, .hyperplane, .unit, .unit] =
      ∑ i, planeZeroExpanded i := by
  have hbind {α β : Type} (s : Multiset α) (f : α → Multiset β) :
      s.bind f = (s.map f).sum := by
    induction s using Multiset.induction_on with
    | empty => rfl
    | cons a s ih =>
      simp only [Multiset.cons_bind, Multiset.map_cons, Multiset.sum_cons, ih]
  have hsum : L24Relation.genusTwoTerms .plane 0 0 0
      ![.hyperplane, .hyperplane, .unit, .unit] = ∑ i, planeZeroColumn i := by
    simp only [L24Relation.genusTwoTerms, L24Relation.surfaceTerms,
      L24Relation.cotangentRelation, CotangentCombination.pullback, Multiset.bind_map,
      CotangentTerm.addMarkings, Multiset.map_singleton, Int.cast_one, mul_one,
      Multiset.bind_singleton]
    rw [hbind]
    simp only [← Finset.sum_eq_multiset_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : L24CorrectionsReplay.fullClaim i = 0
    · simp only [h, ne_eq, not_true_eq_false, if_false, planeZeroColumn,
        RationalTerms.scale, if_true]
    · rw [if_pos h]
      rfl
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ ↦ planeZero_columns_checked i)

set_option maxRecDepth 65536 in
/-- The executable full equation has exactly the held coefficients and residual queries. -/
theorem planeZero_checked : RationalTerms.Equivalent
    (L24Relation.genusTwoTerms .plane 0 0 0 ![.hyperplane, .hyperplane, .unit, .unit])
    planeZero := by
  rw [planeZero_expanded_checked]
  decide +kernel

end AxiomaticGW.SurfaceL24
