/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPRows

/-!
# The shifted genus-two primary equation at the strict transform of a line

At L = H − E₁ − E₂, all four BP rows of the original primary combination
are evaluated at L + E₁ with one extra point. The class-zero boundary
cancels its lower-genus constant. The same-class equation is 6N − 6H = 0.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineBP
open SurfaceGenusTwoBlowupOrder SurfacePolynomialReduction SurfaceGenusTwoBlowupScalar
open SurfaceGenusTwo BelorousskiPandharipande

private abbrev X := SurfaceTarget.blowupTwo
private abbrev shifted : X.Curve := ![1, 0, 1]

-- The first three columns are boundary divisors. The last four are the
-- distinct first descendants at L, including the point descendant.
private def curve (j : Fin 7) : X.Curve := if j < 3 then 0 else line
private def delta (j : Fin 7) : X.Curve := if j < 3 then shifted else X.exceptionalCurve 0
private def label : Fin 7 → SurfaceBasisLabel X :=
  ![.hyperplane, .exceptional 0, .exceptional 1, .hyperplane, .point,
    .exceptional 0, .exceptional 1]
private def points : Fin 7 → ℕ := ![0, 0, 0, 1, 0, 1, 1]
private def variableAt (j : Fin 7) : Variable X :=
  .inr (SurfaceFirstDescendant.query 2 (curve j) (label j) (points j))

private theorem source_eq (j : Fin 7) :
    SurfaceGenusZero.variableCurve (variableAt j) + delta j = shifted := by
  revert j
  decide +kernel

private def paper (j : Fin 7) (i : Fin 4) (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  remainderPointCoefficient X (variableAt j)
    (firstCoefficientVertex X (curve j) (label j) (points j))
    (paperCotangentTerm (Fin.castAdd 16 i)) (delta j) 1 a

private theorem bp_eq (j : Fin 7) (a : Fin 3 → SurfaceBasisLabel X) :
    BelorousskiPandharipande.pointCoefficient X 1 shifted a (variableAt j) =
      ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) *
        ∑ e : Fin 6, paper j i (a ∘ labelPermutation e) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [paper, firstCoefficientVertex_eq]
  change _ = remainderPointCoefficient X (variableAt j) (coefficientVertex X (variableAt j))
    (paperCotangentTerm _) (delta j) 1 (a ∘ labelPermutation e)
  rw [← SurfaceGenusTwoBlowupPCoefficients.remainder_orbit (variableAt j) 1 (delta j) a
    (Fin.castAdd 16 i) e, remainderPointCoefficient_eq X (variableAt j) _ rfl, source_eq]

private theorem not_points (j : Fin 7) (beta : X.Curve) (m : ℕ) :
    Sum.inr (SurfaceQuery.points X 2 beta m) ≠ variableAt j :=
  SurfaceFirstDescendant.query_ne_points _ beta _ _ m

private def mainFlag (j : Fin 7) {k : ℕ} (h : StableArity 2 (Fin k)) (s : Fin k)
    (a : Fin k → SurfaceBasisLabel X) (m : ℕ) : ℚ :=
  let beta := SurfaceGenusZero.variableCurve (variableAt j)
  let q := (SurfaceAncestorKey.ofLabels 2 (Fin k) h beta (Pi.single s 1) a).addPoints m
  if q.DimensionCompatible then
    RationalTerms.coefficient (RationalTerms.rename Sum.inr (SurfaceFirstDescendant.terms
      2 beta (a s) (Multiset.replicate m .point + (Finset.univ.erase s).val.map a))) {variableAt j}
  else 0

private theorem flag_eq (j : Fin 7) {k : ℕ} (h : StableArity 2 (Fin k)) (s : Fin k)
    (a : Fin k → SurfaceBasisLabel X) (m : ℕ) (d : X.Curve) :
    remainderVertex X (variableAt j) (coefficientVertex X (variableAt j)) m 2 (Fin k)
      h (Pi.single s 1) inferInstance d a = if d = 0 then mainFlag j h s a m else 0 := by
  rw [remainderVertex_onePsi_of_not_points (variableAt j) (not_points j),
    coefficient_residualTerms_onePsi_of_not_points (variableAt j) (not_points j)]
  rfl

private def glued {k l : ℕ} (j : Fin 7) (h : StableArity 2 (Fin k)) (s : Fin k)
    (a : SurfaceBasisLabel X → Fin k → SurfaceBasisLabel X)
    (b : SurfaceBasisLabel X → Fin l → SurfaceBasisLabel X) : ℚ :=
  ∑ split ∈ X.splittings (delta j), ∑ t : SurfaceBasisLabel X, t.inverseWeight *
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal 1, (Nat.choose 1 ij.1 : ℚ) *
      ((if split.1 = 0 then mainFlag j h s (a t) ij.1 else 0) *
        SurfaceGenusZero.primaryScalar X (SurfacePointBenchmarkCache.genusZero X)
          split.2 ij.2 (b t.dual))

private def tail {l : ℕ} (j : Fin 7) (n : ℕ) (a : Fin l → SurfaceBasisLabel X) : ℚ :=
  if ((∑ t, (a t).codimension : ℕ) : ℤ) + (n : ℤ) =
      X.c1Degree (delta j) - 1 + (l : ℤ) then ∏ t, (a t).primaryFactor (delta j) else 0

-- The first-descendant coefficient forces the left class to its requested class.
-- The full remainder is on the rational component, whose point invariant is one.
private theorem glued_eq {k l : ℕ} (j : Fin 7) (h : StableArity 2 (Fin k)) (s : Fin k)
    (a : SurfaceBasisLabel X → Fin k → SurfaceBasisLabel X)
    (b : SurfaceBasisLabel X → Fin l → SurfaceBasisLabel X) :
    glued j h s a b = ∑ t : SurfaceBasisLabel X, t.inverseWeight *
      (mainFlag j h s (a t) 0 * tail j 1 (b t.dual) +
        mainFlag j h s (a t) 1 * tail j 0 (b t.dual)) := by
  have hpos : delta j ≠ 0 := by revert j; decide +kernel
  have hv : SurfacePointBenchmarkCache.genusZero X (delta j) = 1 := by revert j; decide +kernel
  have had : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide +kernel
  rw [glued, Finset.sum_eq_single (0, delta j)]
  · simp only [had, Finset.sum_insert (show (0, 1) ∉ ({(1, 0)} : Finset (ℕ × ℕ)) by decide),
      Finset.sum_singleton, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul,
      if_true, SurfaceGenusZero.primaryScalar, hv, one_ne_zero, and_false, if_false, hpos,
      mul_one, tail, Fintype.card_fin]
  · intro p hp hne
    have hn : p.1 ≠ 0 := by
      intro hz
      rw [X.splittings_eq] at hp
      have he := (X.effective.mem_splittings _ _ _).mp hp
      exact hne (Prod.ext hz (by simpa only [hz, zero_add] using he))
    simp only [hn, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
  · intro hm
    rw [X.splittings_eq] at hm
    exact (hm ((X.effective.mem_splittings _ _ _).mpr (zero_add _))).elim

private def scalar (j : Fin 7) (i : Fin 4) (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  match i.val with
  | 0 => 0
  | 1 => glued j (by norm_num [StableArity]) (0 : Fin 1)
      (fun t ↦ ![t]) (fun t ↦ ![a 0, a 1, a 2, t])
  | k => glued j (by norm_num [StableArity]) (if k = 2 then 0 else (1 : Fin 2))
      (fun t ↦ ![a 0, t]) (fun t ↦ ![a 1, a 2, t])

private theorem pair_eq (j : Fin 7) (z : Fin 2) (lab : Fin 3 → SurfaceBasisLabel X) :
    remainderPointCoefficient X (variableAt j) (coefficientVertex X (variableAt j))
      (paperCotangentTerm (if z = 0 then 2 else 3)) (delta j) 1 lab =
    glued j (by norm_num [StableArity]) z (fun t ↦ ![lab 0, t])
      (fun t ↦ ![lab 1, lab 2, t]) := by
  have hc : lab = ![lab 0, lab 1, lab 2] := by funext t; fin_cases t <;> rfl
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X (variableAt j) (coefficientVertex X (variableAt j))
      (paperCotangentTerm (if z = 0 then 2 else 3)) (delta j) 1 lab =
    remainderContraction X (variableAt j) (remainderVertex X (variableAt j)
      (coefficientVertex X (variableAt j))) (GetzlerGraphs.join (m := 1) (n := 2) 1 2
      (GluingExpression.fundamental 2 (Fin 2) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 3) (by norm_num [StableArity])))
      (by exact (Pi.single z 1, (0 : Fin 3 → ℕ)))
      (by exact ((inferInstance : DecidableEq (Fin 2)), (inferInstance : DecidableEq (Fin 3))))
      (delta j) 1 ![lab 0, lab 1, lab 2] := by
    conv_lhs => rw [hc]
    rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl
    · rw [if_pos (by decide), ← h0]
      rfl
    · rw [if_neg (by decide), ← h1]
      rfl
  rw [he, SurfaceGenusTwoBlowupPCoefficients.pair_join]
  simp only [remainderContraction, ite_true, flag_eq, glued,
    SurfacePointBenchmarkCache.genusZero_eq]

private theorem paper_scalar (j : Fin 7) (i : Fin 4) (a : Fin 3 → SurfaceBasisLabel X) :
    paper j i a = scalar j i a := by
  have hx (i : Fin 4) : (paperCotangentTerm (Fin.castAdd 16 i)).expression.maxComponentGenus = 2 :=
    by revert i; decide +kernel
  rw [paper, firstCoefficientVertex_eq]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · exact SurfaceGenusTwoBlowupPCoefficients.paper_zero _ (not_points j) _ _ _
  · change remainderPointCoefficient X (variableAt j) (coefficientVertex X (variableAt j))
      (paperCotangentTerm (Fin.castAdd 16 (1 : Fin 4))) _ _ _ = _
    rw [remainderPointCoefficient, if_pos (hx 1)]
    change remainderContraction X (variableAt j) (remainderVertex X (variableAt j)
      (coefficientVertex X (variableAt j))) (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (GluingExpression.fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (GluingExpression.fundamental 0 (Fin 4) (by norm_num [StableArity])))
      (![1], (0 : Fin 4 → ℕ))
      ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4)))
      (delta j) 1 a = _
    have hl (t : SurfaceBasisLabel X) :
        (Option.elim · t ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
          finSuccEquiv' 0 = ![t] := by funext z; fin_cases z; rfl
    have hr (t : SurfaceBasisLabel X) :
        (Option.elim · t ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
          finSuccEquiv' 3 = ![a 0, a 1, a 2, t] := by funext z; fin_cases z <;> rfl
    have hk : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := by decide +kernel
    simp only [GetzlerGraphs.join, remainderContraction, ite_true,
      GluingExpression.pointContraction, primaryPointVertex, and_self, hl, hr, hk, flag_eq,
      scalar, glued,
      SurfacePointBenchmarkCache.genusZero_eq]
    rfl
  · exact pair_eq j 0 a
  · exact pair_eq j 1 a

-- A first-descendant column survives exactly when the flagged label and
-- point count agree. A second primary divisor contributes its full signed pairing.
private def oneFlag (j : Fin 7) (t : SurfaceBasisLabel X) (m : ℕ) : ℚ :=
  if t = label j ∧ m = points j then 1 else 0

private def twoFlags (j : Fin 7) (s : Fin 2) (u t : SurfaceBasisLabel X) (m : ℕ) : ℚ :=
  let a := (![u, t] : Fin 2 → SurfaceBasisLabel X)
  let b := a (1 - s)
  if a s = label j ∧ b ≠ .unit ∧ m + (if b = .point then 1 else 0) = points j then
    b.primaryFactor (curve j)
  else 0

private theorem oneFlag_eq (j : Fin 7) (t : SurfaceBasisLabel X) (m : Fin 2) :
    mainFlag j (by norm_num [StableArity]) (0 : Fin 1) ![t] m.val = oneFlag j t m.val := by
  revert j t m
  decide +kernel

private theorem twoFlags_eq (j : Fin 7) (s : Fin 2) (u t : SurfaceBasisLabel X) (m : Fin 2) :
    mainFlag j (by norm_num [StableArity]) s ![u, t] m.val = twoFlags j s u t m.val := by
  revert j s u t m
  decide +kernel

private def fastScalar (j : Fin 7) (i : Fin 4) (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  match i.val with
  | 0 => 0
  | 1 => ∑ t : SurfaceBasisLabel X, t.inverseWeight *
      (oneFlag j t 0 * tail j 1 ![a 0, a 1, a 2, t.dual] +
       oneFlag j t 1 * tail j 0 ![a 0, a 1, a 2, t.dual])
  | k => ∑ t : SurfaceBasisLabel X, t.inverseWeight *
      (twoFlags j (if k = 2 then 0 else 1) (a 0) t 0 * tail j 1 ![a 1, a 2, t.dual] +
       twoFlags j (if k = 2 then 0 else 1) (a 0) t 1 * tail j 0 ![a 1, a 2, t.dual])

private theorem scalar_fast (j : Fin 7) (i : Fin 4) (a : Fin 3 → SurfaceBasisLabel X) :
    scalar j i a = fastScalar j i a := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · rfl
  · have h10 (t : SurfaceBasisLabel X) :
      mainFlag j (by norm_num [StableArity]) 0 ![t] 0 = oneFlag j t 0 := oneFlag_eq j t 0
    have h11 (t : SurfaceBasisLabel X) :
      mainFlag j (by norm_num [StableArity]) 0 ![t] 1 = oneFlag j t 1 := oneFlag_eq j t 1
    simp only [scalar, fastScalar, Fin.val_one, glued_eq, h10, h11]
  all_goals
    have h20 (s : Fin 2) (t : SurfaceBasisLabel X) :
        mainFlag j (by norm_num [StableArity]) s ![a 0, t] 0 = twoFlags j s (a 0) t 0 :=
      twoFlags_eq j s _ t 0
    have h21 (s : Fin 2) (t : SurfaceBasisLabel X) :
        mainFlag j (by norm_num [StableArity]) s ![a 0, t] 1 = twoFlags j s (a 0) t 1 :=
      twoFlags_eq j s _ t 1
    simp only [scalar, fastScalar, glued_eq, h20, h21]

private def triple : Fin 4 → Fin 3 → SurfaceBasisLabel X :=
  ![![.exceptional 0, .hyperplane, .hyperplane], ![.exceptional 0, .exceptional 0, .hyperplane],
    ![.exceptional 0, .exceptional 0, .exceptional 0], ![.hyperplane, .hyperplane, .hyperplane]]

private def bp (j : Fin 7) (r : Fin 4) : ℚ :=
  ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) *
    ∑ e : Fin 6, paper j i (triple r ∘ labelPermutation e)

private def entries : Fin 7 → Fin 4 → ℚ := ![
  ![0, 0, 0, 12], ![0, 0, 0, 0], ![0, 0, 0, -12], ![0, 6, 0, 0],
  ![0, 0, 0, 0], ![0, -6, -12, 0], ![0, 0, 0, 0]]

set_option Elab.async false
set_option maxRecDepth 20000

private theorem computed (j : Fin 7) (r : Fin 4) : bp j r = entries j r := by
  unfold bp
  simp_rw [paper_scalar, scalar_fast]
  revert j r
  decide +kernel

private theorem combined_entries (j : Fin 7) :
    3 / 2 * entries j 0 + (-1) * entries j 1 + 1 / 2 * entries j 2 +
      (-1 / 3) * entries j 3 = (![-4, 0, 4, -6, 0, 0, 0] : Fin 7 → ℚ) j := by
  revert j
  decide +kernel

private theorem weighted (j : Fin 7) :
    singletonCoefficient 0 (line, .primary) (variableAt j) =
      (![-4, 0, 4, -6, 0, 0, 0] : Fin 7 → ℚ) j := by
  have h (r : Fin 4) : BelorousskiPandharipande.pointCoefficient X 1 shifted
      (triple r) (variableAt j) = entries j r := (bp_eq j _).trans (computed j r)
  have hd : X.planeDegree line = 1 := by decide +kernel
  have he : X.effective.energy line = 1 := by decide +kernel
  have hs : line + X.exceptionalCurve 0 = shifted := by decide +kernel
  simp only [singletonCoefficient, hd, he, hs, Nat.cast_one, mul_one]
  let c (r : Fin 4) :=
    BelorousskiPandharipande.pointCoefficient X 1 shifted (triple r) (variableAt j)
  change 3 / 2 * c 0 + (-1) * c 1 + 1 / 2 * c 2 + (-1 / 3) * c 3 = _
  change ∀ r, c r = entries j r at h
  rw [h 0, h 1, h 2, h 3]
  exact combined_entries j

/-- The shifted primary BP equation reconstructs the same value as the H equation at L. -/
theorem primary_eq_hyperplane : SurfaceGenusTwoBlowupRecursion.values 0 (line, .primary) =
    SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) := by
  have h := reduced_row .primary
  rw [primary_constant, Fin.sum_univ_five, Fin.sum_univ_five] at h
  let v := SurfaceGenusTwoBlowupRecursion.values (X := X) 0
  let c (beta : X.Curve) (f : Family X) :=
    singletonCoefficient 0 (line, .primary) (.inr (f.query beta))
  change -1 / 360 + ((c 0 .hyperplane * (-1 / 960) + c 0 .point * 0 + c 0 .primary * 0 +
    c 0 (.exceptional 0) * (-1 / 2880) + c 0 (.exceptional 1) * (-1 / 2880)) +
    (c line .hyperplane * v (line, .hyperplane) + c line .point * v (line, .point) +
    c line .primary * v (line, .primary) + c line (.exceptional 0) * v (line, .exceptional 0) +
    c line (.exceptional 1) * v (line, .exceptional 1))) = 0 at h
  have hN : c line .primary = 6 := by
    unfold c
    rw [singletonCoefficient_eq]
    exact (SurfaceGenusTwoBlowupNCoefficients.row_primary_coefficient 0 line).trans
      (by decide +kernel)
  have hH₀ : c 0 .hyperplane = -4 := weighted 0
  have hE₀ : c 0 (.exceptional 0) = 0 := weighted 1
  have hE₁ : c 0 (.exceptional 1) = 4 := weighted 2
  have hH : c line .hyperplane = -6 := weighted 3
  have hP : c line .point = 0 := weighted 4
  have hK₁ : c line (.exceptional 0) = 0 := weighted 5
  have hK₂ : c line (.exceptional 1) = 0 := weighted 6
  rw [hH₀, hE₀, hE₁, hH, hP, hN, hK₁, hK₂] at h
  change v (line, .primary) = v (line, .hyperplane)
  linarith only [h]

/-- All five canonical genus-two families agree at the strict transform of the line. -/
theorem family_eq_hyperplane (f : Family .blowupTwo) :
    SurfaceGenusTwoBlowupRecursion.values 0 (line, f) =
      SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane) := by
  cases f with
  | hyperplane => rfl
  | point => exact point_eq_hyperplane
  | primary => exact primary_eq_hyperplane
  | exceptional i => exact (exceptional_eq_point i).trans point_eq_hyperplane

end AxiomaticGW.BlowupTwoLineBP
