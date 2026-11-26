/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupPCoefficients

/-! # Exact BP scalars for a requested first descendant at arbitrary effective remainder

For a nonprimary column the primary main diagram vanishes. Each of the other
three diagrams has one cotangent power on the genus-two component. Its signed
pullbacks can be replaced by the existing first-descendant normalization at
the requested class, with every point placement and rational node retained.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBPFirstScalar
open SurfaceGenusTwo SurfacePolynomialReduction SurfaceGenusTwoBlowupPCoefficients
open GluingExpression BelorousskiPandharipande
variable {X : SurfaceTarget}

set_option maxRecDepth 20000

/-- The signed one-power pullback has a nonprimary coefficient only at zero main remainder. -/
def main (v : Variable X) (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity 2 S) (s : S) (delta : X.Curve) (a : S → SurfaceBasisLabel X) : ℚ :=
  let beta := SurfaceGenusZero.variableCurve v
  let q := (SurfaceAncestorKey.ofLabels 2 S h beta (Pi.single s 1) a).addPoints n
  if delta = 0 ∧ q.DimensionCompatible then
    RationalTerms.coefficient (RationalTerms.rename Sum.inr
      (SurfaceFirstDescendant.terms 2 beta (a s)
        (Multiset.replicate n .point + (Finset.univ.erase s).val.map a))) {v}
  else 0

private theorem main_eq (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v) (n : ℕ)
    {S : Type} [Fintype S] [DecidableEq S] (h : StableArity 2 S) (s : S)
    (delta : X.Curve) (a : S → SurfaceBasisLabel X) :
    remainderVertex X v (coefficientVertex X v) n 2 S h (Pi.single s 1) inferInstance delta a =
      main v n h s delta a := by
  rw [remainderVertex_onePsi_of_not_points v hv,
    coefficient_residualTerms_onePsi_of_not_points v hv]
  unfold main
  by_cases he : delta = 0 <;> simp only [he, ite_true, ite_false, true_and, false_and]

/-- One genus-two node flag, opposite a four-flag primary rational vertex. -/
def one (v : Variable X) (rational : X.Curve → ℚ) (delta : X.Curve) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) :=
  ∑ split ∈ X.splittings delta, ∑ t : SurfaceBasisLabel X, t.inverseWeight *
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (main v ij.1 (by norm_num [StableArity] : StableArity 2 (Fin 1)) 0 split.1 ![t] *
        SurfaceGenusZero.primaryScalar X rational split.2 ij.2 ![a 0, a 1, a 2, t.dual])

private theorem paper_one_eq (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v) (paperCotangentTerm 1) delta n a =
      one v (SurfaceGenusZero.pointValue X) delta n a := by
  rw [remainderPointCoefficient, if_pos (by decide +kernel)]
  change remainderContraction X v (remainderVertex X v (coefficientVertex X v))
    (GetzlerGraphs.join (m := 0) (n := 3) 0 3
      (fundamental 2 (Fin 1) (by norm_num [StableArity]))
      (fundamental 0 (Fin 4) (by norm_num [StableArity])))
    (![1], (0 : Fin 4 → ℕ))
    ((inferInstance : DecidableEq (Fin 1)), (inferInstance : DecidableEq (Fin 4))) delta n a = _
  have hl (t : SurfaceBasisLabel X) :
      (Option.elim · t ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inl)) ∘
        finSuccEquiv' 0 = ![t] := by funext i; fin_cases i; rfl
  have hr (t : SurfaceBasisLabel X) :
      (Option.elim · t ((a ∘ (finSumFinEquiv : Fin 0 ⊕ Fin 3 ≃ Fin 3)) ∘ Sum.inr)) ∘
        finSuccEquiv' 3 = ![a 0, a 1, a 2, t] := by funext i; fin_cases i <;> rfl
  have hp : (![1] : Fin 1 → ℕ) = Pi.single 0 1 := by decide +kernel
  simp only [GetzlerGraphs.join, remainderContraction, ite_true,
    GluingExpression.pointContraction, hl, hr, primaryPointVertex, and_self, hp, one, main_eq v hv]

/-- One original marking and one node flag on the genus-two component.
The cotangent power may lie on either flag. -/
def pair (v : Variable X) (rational : X.Curve → ℚ) (delta : X.Curve) (n : ℕ)
    (s : Fin 2) (a : Fin 3 → SurfaceBasisLabel X) :=
  ∑ split ∈ X.splittings delta, ∑ t : SurfaceBasisLabel X, t.inverseWeight *
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : ℚ) *
      (main v ij.1 (by norm_num [StableArity] : StableArity 2 (Fin 2)) s split.1 ![a 0, t] *
        SurfaceGenusZero.primaryScalar X rational split.2 ij.2 ![a 1, a 2, t.dual])

private theorem paper_pair_eq (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (delta : X.Curve) (n : ℕ) (s : Fin 2) (a : Fin 3 → SurfaceBasisLabel X) :
    remainderPointCoefficient X v (coefficientVertex X v)
      (paperCotangentTerm (if s = 0 then 2 else 3)) delta n a =
      pair v (SurfaceGenusZero.pointValue X) delta n s a := by
  have h0 : (![1, 0] : Fin 2 → ℕ) = Pi.single 0 1 := by decide +kernel
  have h1 : (![0, 1] : Fin 2 → ℕ) = Pi.single 1 1 := by decide +kernel
  have he : remainderPointCoefficient X v (coefficientVertex X v)
      (paperCotangentTerm (if s = 0 then 2 else 3)) delta n a =
      remainderContraction X v (remainderVertex X v (coefficientVertex X v))
        (GetzlerGraphs.join (m := 1) (n := 2) 1 2
          (fundamental 2 (Fin 2) (by norm_num [StableArity]))
          (fundamental 0 (Fin 3) (by norm_num [StableArity])))
        (by exact (Pi.single s 1, (0 : Fin 3 → ℕ)))
        (by exact ((inferInstance : DecidableEq (Fin 2)), (inferInstance : DecidableEq (Fin 3))))
        delta n a := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · rw [if_pos rfl, ← h0]
      rfl
    · rw [if_neg (by decide : (1 : Fin 2) ≠ 0), ← h1]
      rfl
  have ha : a = ![a 0, a 1, a 2] := by funext i; fin_cases i <;> rfl
  rw [he]
  conv_lhs => rw [ha, pair_join]
  simp only [remainderContraction, ite_true, main_eq v hv, pair]

/-- All six ordered assignments of each surviving BP diagram, including its original weight. -/
def row (v : Variable X) (rational : X.Curve → ℚ) (delta : X.Curve) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  2 * (∑ e : Fin 6, one v rational delta n (a ∘ labelPermutation e)) +
  3 * (∑ e : Fin 6, pair v rational delta n 0 (a ∘ labelPermutation e)) -
  3 * (∑ e : Fin 6, pair v rational delta n 1 (a ∘ labelPermutation e))

/-- Equality to the original signed singleton coefficient at its full source class. -/
theorem row_eq (v : Variable X)
    (hv : ∀ beta n, Sum.inr (SurfaceQuery.points X 2 beta n) ≠ v)
    (rational : X.Curve → ℚ) (hr : rational = SurfaceGenusZero.pointValue X)
    (delta : X.Curve) (n : ℕ) (a : Fin 3 → SurfaceBasisLabel X) :
    row v rational delta n a = BelorousskiPandharipande.pointCoefficient X n
      (SurfaceGenusZero.variableCurve v + delta) a v := by
  rw [hr]
  simp only [BelorousskiPandharipande.pointCoefficient, ← remainderPointCoefficient_eq X v _ rfl,
    remainder_orbit, Fin.sum_univ_four]
  change _ = -2 * (∑ e : Fin 6, remainderPointCoefficient X v _ (paperCotangentTerm 0) _ _
    (a ∘ labelPermutation e)) + 2 * (∑ e : Fin 6, remainderPointCoefficient X v _
    (paperCotangentTerm 1) _ _ (a ∘ labelPermutation e)) +
    3 * (∑ e : Fin 6, remainderPointCoefficient X v _ (paperCotangentTerm 2) _ _
      (a ∘ labelPermutation e)) + -3 * (∑ e : Fin 6, remainderPointCoefficient X v _
        (paperCotangentTerm 3) _ _ (a ∘ labelPermutation e))
  have h₂ := paper_pair_eq v hv delta n 0
  have h₃ := paper_pair_eq v hv delta n 1
  simp only [ite_true, if_neg (by decide : (1 : Fin 2) ≠ 0)] at h₂ h₃
  simp only [paper_zero v hv, Finset.sum_const_zero, mul_zero, zero_add, paper_one_eq v hv,
    h₂, h₃, row, neg_mul, sub_eq_add_neg]

end AxiomaticGW.SurfaceGenusTwoBPFirstScalar
