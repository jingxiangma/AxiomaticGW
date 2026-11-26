/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoConstant
public import AxiomaticGW.Surfaces.PlaneGenusTwoRemainder

/-!
# Reuse certified rational values in plane coefficient replay

The original effective-remainder contraction repeatedly evaluates rational
primary values. This implementation reuses the proved plane table, with the
original algorithm outside its bound. Zero main-component coefficients also
avoid unnecessary rational contractions. Both changes preserve the complete
signed coefficient, including every cotangent tail and binomial weight.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction
open SurfaceGenusZero (variableCurve)

private theorem mulSkipZero (a b : ℚ) : (if a = 0 then 0 else a * b) = a * b := by
  by_cases ha : a = 0
  · rw [if_pos ha, ha, zero_mul]
  · exact if_neg ha

/-- Only the rational primary evaluation changes implementation. -/
def planeCachedPointVertex (v : Variable .plane) (n : ℕ) :
    SurfaceCotangentVertexValues .plane ℚ :=
  fun g S _ h d l beta a ↦
    if g = 0 ∧ d = 0 then
      SurfaceGenusZero.primaryScalar .plane planeRationalPointValue beta n a
    else SurfacePointPullback.vertex .plane (coefficientVertex .plane v) n g S h d l beta a

theorem planeCachedPointVertex_eq (v : Variable .plane) :
    planeCachedPointVertex v = primaryPointVertex .plane v := by
  funext n g S _ h d l beta a
  simp only [planeCachedPointVertex, primaryPointVertex, planeRationalPointValue_eq]

/-- Follow the same main component and use certified rational primary values. -/
def planeCachedRemainderContraction (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ) :
    {g : ℕ} → {S : Type} → [Fintype S] → (x : GluingExpression g S) →
      x.CotangentDecoration → x.DecidableLabels → SurfaceTarget.plane.Curve → ℕ →
        (S → SurfaceBasisLabel .plane) → ℚ
  | _, _, _, @GluingExpression.fundamental g S _ h, d, l, delta, n, a =>
      if g = 2 then main n g S h d l delta a else 0
  | _, _, _, @GluingExpression.relabel _ _ _ _ _ e x, d, l, delta, n, a =>
      planeCachedRemainderContraction v main x d l delta n (a ∘ e)
  | _, _, _, @GluingExpression.separating g h _ _ _ _ x y, d, l, delta, n, a =>
      if g = 2 then
        ∑ split ∈ SurfaceTarget.plane.splittings delta, ∑ b : SurfaceBasisLabel .plane,
          b.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            (n.choose ij.1 : ℚ) *
              (let c := planeCachedRemainderContraction v main x d.1 l.1 split.1 ij.1
                  (Option.elim · b (a ∘ Sum.inl))
               if c = 0 then 0 else c *
                 y.pointContraction .plane (planeCachedPointVertex v)
                   d.2 l.2 split.2 ij.2 (Option.elim · b.dual (a ∘ Sum.inr)))
      else if h = 2 then
        ∑ split ∈ SurfaceTarget.plane.splittings delta, ∑ b : SurfaceBasisLabel .plane,
          b.inverseWeight * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            (n.choose ij.1 : ℚ) *
              (let c := planeCachedRemainderContraction v main y d.2 l.2 split.2 ij.2
                  (Option.elim · b.dual (a ∘ Sum.inr))
               if c = 0 then 0 else c *
                 x.pointContraction .plane (planeCachedPointVertex v)
                   d.1 l.1 split.1 ij.1 (Option.elim · b (a ∘ Sum.inl)))
      else 0
  | _, _, _, @GluingExpression.nonseparating _ _ _ _, _, _, _, _, _ => 0

/-- No branch or coefficient is removed except a product already proved zero. -/
theorem planeCachedRemainderContraction_eq (v : Variable .plane)
    (main : ℕ → SurfaceCotangentVertexValues .plane ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (d : x.CotangentDecoration) (l : x.DecidableLabels)
    (delta : SurfaceTarget.plane.Curve) (n : ℕ) (a : S → SurfaceBasisLabel .plane) :
    planeCachedRemainderContraction v main x d l delta n a =
      remainderContraction .plane v main x d l delta n a := by
  induction x generalizing delta n with
  | fundamental g S h => rfl
  | relabel e x ih => exact ih d l delta n (a ∘ e)
  | separating x y ihx ihy =>
    simp only [planeCachedRemainderContraction, remainderContraction,
      planeCachedPointVertex_eq, mulSkipZero, ihx, ihy]
    split_ifs <;> try rfl
    apply Finset.sum_congr rfl
    intro split _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply Finset.sum_congr rfl
    intro ij _
    rw [mul_comm (remainderContraction .plane v main y _ _ _ _ _)]
  | nonseparating x ih => rfl

/-- Signed point pullback uses the same smaller point counts and terminal coefficient. -/
def planeCachedRemainderVertex (v : Variable .plane) (n : ℕ) :
    SurfaceCotangentVertexValues .plane ℚ :=
  fun g S _ h d l delta a ↦
    if g = 2 ∧ d = 0 then
      if delta = 0 then
        RationalTerms.coefficient (RationalTerms.affineSubstitute normalizedTerms
          (residualTerms ((SurfaceAncestorKey.ofLabels g S h (variableCurve v) 0 a).addPoints n)))
          {v}
      else 0
    else match n with
    | 0 => planeCoefficientVertex v g S h (variableCurve v + delta) d a
    | n + 1 =>
      (((GluingExpression.fundamental g S h).addCotangentMarking d l).map fun t ↦
        t.1 * planeCachedRemainderContraction v
          (fun m ↦ if _hm : m ≤ n then planeCachedRemainderVertex v m
            else fun _ _ _ _ _ _ _ _ ↦ 0)
          t.2.expression t.2.decoration t.2.labels delta n (Option.elim · .point a)).sum
termination_by n
decreasing_by omega

theorem planeCachedRemainderVertex_eq (v : Variable .plane) (n : ℕ) :
    planeCachedRemainderVertex v n = remainderVertex .plane v (planeCoefficientVertex v) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    funext g S _ h d l delta a
    by_cases hp : g = 2 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := hp
      rw [planeCachedRemainderVertex.eq_def, if_pos ⟨rfl, rfl⟩, remainderVertex_plane_primary]
    · cases n with
      | zero => rw [planeCachedRemainderVertex.eq_def, if_neg hp, remainderVertex]
      | succ n =>
        rw [planeCachedRemainderVertex.eq_def, if_neg hp, remainderVertex]
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro t _
        rw [planeCachedRemainderContraction_eq]
        congr 1
        congr 1
        funext m
        by_cases hm : m ≤ n
        · rw [dif_pos hm, dif_pos hm, ih m (by omega)]
        · rw [dif_neg hm, dif_neg hm]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande
open SurfacePolynomialReduction SurfaceGenusTwo
open SurfaceGenusZero (variableCurve)

/-- Cached scalar coefficient at the complete requested effective remainder. -/
def planeCachedRemainderPointCoefficient (n : ℕ) (delta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) : ℚ :=
  ∑ i : Fin 4, rawPaperCoefficient (Fin.castAdd 16 i) * ∑ e,
    let z := orbitCotangentTerm (Fin.castAdd 16 i) e
    if z.expression.maxComponentGenus = 2 then
      planeCachedRemainderContraction v (planeCachedRemainderVertex v) z.expression
        z.decoration z.labels delta n a
    else 0

theorem planeCachedRemainderPointCoefficient_eq (n : ℕ) (delta : SurfaceTarget.plane.Curve)
    (a : Fin 3 → SurfaceBasisLabel .plane) (v : Variable .plane) :
    planeCachedRemainderPointCoefficient n delta a v =
      planeRemainderPointCoefficient n delta a v := by
  have hv : planeCachedRemainderVertex v =
      remainderVertex .plane v (planeCoefficientVertex v) :=
    funext (planeCachedRemainderVertex_eq v)
  simp only [planeCachedRemainderPointCoefficient, planeRemainderPointCoefficient,
    remainderPointCoefficient, planeCachedRemainderContraction_eq, hv]

/-- Preserve the absolute source-degree guard before subtracting the requested class. -/
def planeCachedPointCoefficient (n source : ℕ) (a : Fin 3 → SurfaceBasisLabel .plane)
    (v : Variable .plane) : ℚ :=
  if variableCurve v 0 ≤ source then
    planeCachedRemainderPointCoefficient n ![source - variableCurve v 0] a v else 0

theorem planeCachedPointCoefficient_eq (n source : ℕ) (a : Fin 3 → SurfaceBasisLabel .plane)
    (v : Variable .plane) :
    planeCachedPointCoefficient n source a v = planePointCoefficientByRemainder n source a v := by
  simp only [planeCachedPointCoefficient, planePointCoefficientByRemainder,
    planeCachedRemainderPointCoefficient_eq]

end AxiomaticGW.BelorousskiPandharipande
