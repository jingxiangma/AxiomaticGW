/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoConstant
public import AxiomaticGW.Surfaces.GenusOneDimension
public import AxiomaticGW.Surfaces.PrimaryPointPullback
public import AxiomaticGW.Surfaces.ScalarPointContraction

/-!
# Primary scalar shortcuts for BP constants

Undecorated lower-genus components are evaluated directly from their point
values. The shortcut preserves signed dimension, classical and elliptic
zero-degree terms, divisor factors and every counted point. It can reuse
already certified primary tables without assuming new seed values.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceGenusTwo
open SurfacePolynomialReduction

/-- Primary lower-genus reconstruction agrees with the original term reduction. -/
theorem constant_primary_eq {X : SurfaceTarget} (q : SurfaceAncestorKey X)
    (hg : q.genus ≤ 1) (hp : q.IsPrimary) :
    (if q.DimensionCompatible then
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q else 0) =
      RationalTerms.eval (SurfaceGenusOne.pointValuation
        (SurfaceGenusZero.pointValue X) (SurfaceGenusOne.pointValue X)) (primaryTerms q) := by
  rw [SurfaceGenusOne.eval_primaryTerms_curve _ _ q hg hp]
  by_cases hd : q.DimensionCompatible
  · rw [if_pos hd, if_pos hd]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg with hg | hg
    · rw [SurfaceGenusOne.componentValue, if_pos hg,
        SurfaceGenusZero.ancestorValue, q.totalPsi_eq_zero_iff.mpr hp,
        SurfaceGenusZero.ancestorValueFuel, if_pos ⟨hg, hp⟩, if_pos hg]
      unfold SurfaceGenusZero.primaryValue
      by_cases hb : q.beta = 0
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb]
        by_cases hc : q.primaryCoefficient = 0
        · change (if _ then q.primaryCoefficient * _ else 0) = _
          simp only [hc, zero_mul, ite_self]
        · rw [if_pos (q.point_count_of_genus_zero hg hp hd hc), if_pos hg]
          rfl
    · have hne : q.genus ≠ 0 := by omega
      rw [SurfaceGenusOne.componentValue, if_neg hne,
        SurfaceGenusOne.ancestorValue, q.totalPsi_eq_zero_iff.mpr hp,
        SurfaceGenusOne.ancestorValueFuel, if_pos ⟨hg, hp⟩, if_neg hne]
      unfold SurfaceGenusOne.primaryValue
      by_cases hb : q.beta = 0
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb]
        by_cases hc : q.primaryCoefficient = 0
        · change (if _ then q.primaryCoefficient * _ else 0) = _
          simp only [hc, zero_mul, ite_self]
        · have hn : q.primaryLabels.count .point = X.effective.energy q.beta := by
            simpa only [hg, Nat.add_sub_cancel] using q.point_count_of_primary hp hd hc
          rw [if_pos hn, if_neg hne]
          rfl
  · rw [if_neg hd, if_neg hd]

/-- Signed pullback of an undecorated component has the exact primary scalar value. -/
theorem vertex_primary_constant_eq (X : SurfaceTarget) (g : ℕ) (hg : g ≤ 1)
    (n : ℕ) (S : Type) [Fintype S] (h : StableArity g S) (l : DecidableEq S)
    (beta : X.Curve) (a : S → SurfaceBasisLabel X) :
    SurfacePointPullback.vertex X (constantVertex X) n g S h 0 l beta a =
      SurfaceGenusOne.primaryScalar X (SurfaceGenusZero.pointValue X)
        (SurfaceGenusOne.pointValue X) g beta n a := by
  rw [SurfacePointPullback.vertex_primary_eq X (constantVertex X)
    (fun q ↦ if q.DimensionCompatible then
      SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q else 0) g
    (fun T _ h gamma b ↦ by rw [constantVertex, if_pos hg])]
  rw [SurfaceGenusOne.primaryScalar_eq _ _ g S h hg beta n a]
  apply constant_primary_eq _ hg
  intro s hs
  rcases Multiset.mem_add.mp hs with hs | hs
  · exact congrArg SurfaceInsertion.psi (Multiset.mem_replicate.mp hs).2
  · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    rfl

/-- Use direct primary scalars only for undecorated lower-genus vertices.
Other components retain their original signed point recursion. -/
def primaryConstantPointVertex (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ) (n : ℕ) :
    SurfaceCotangentVertexValues X ℚ :=
  fun g S _ h d l beta a ↦
    if g ≤ 1 ∧ d = 0 then SurfaceGenusOne.primaryScalar X v₀ v₁ g beta n a
    else SurfacePointPullback.vertex X (constantVertex X) n g S h d l beta a

/-- Reusing point values changes no component of the complete contraction. -/
theorem primaryConstantPointVertex_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (hzero : v₀ = SurfaceGenusZero.pointValue X) (hone : v₁ = SurfaceGenusOne.pointValue X) :
    primaryConstantPointVertex X v₀ v₁ = SurfacePointPullback.vertex X (constantVertex X) := by
  subst v₀
  subst v₁
  funext n g S _ h d l beta a
  unfold primaryConstantPointVertex
  split_ifs with hp
  · obtain ⟨hg, rfl⟩ := hp
    exact (vertex_primary_constant_eq X g hg n S h l beta a).symm
  · rfl

/-- A primary graph with low-genus components may have larger total genus.
Its scalar contraction is exactly the original complete point contraction. -/
theorem primaryGraphEval_pointContraction_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    {g : ℕ} {S : Type} [Fintype S] (x : GluingExpression g S)
    (hg : x.maxComponentGenus ≤ 1) (l : x.DecidableLabels)
    (beta : X.Curve) (n : ℕ) (a : S → SurfaceBasisLabel X) :
    SurfaceGenusOne.primaryGraphEval X v₀ v₁ x beta n a =
      x.pointContraction X (primaryConstantPointVertex X v₀ v₁)
        x.zeroDecoration l beta n a := by
  have hz (u v : ℚ) : (if u = 0 then 0 else u * v) = u * v := by
    split_ifs with h
    · rw [h, zero_mul]
    · rfl
  induction x generalizing beta n with
  | fundamental g S h =>
    change g ≤ 1 at hg
    simp only [SurfaceGenusOne.primaryGraphEval, GluingExpression.pointContraction,
      GluingExpression.zeroDecoration, primaryConstantPointVertex]
    rw [if_pos (show g ≤ 1 ∧ (fun _ : S ↦ (0 : ℕ)) = (0 : S → ℕ) from ⟨hg, rfl⟩)]
  | relabel e x ih => exact ih hg l beta n (a ∘ e)
  | separating x y ihx ihy =>
    change max x.maxComponentGenus y.maxComponentGenus ≤ 1 at hg
    simp only [SurfaceGenusOne.primaryGraphEval, GluingExpression.pointContraction,
      GluingExpression.zeroDecoration, hz, ihx (max_le_iff.mp hg).1 l.1,
      ihy (max_le_iff.mp hg).2 l.2, Algebra.algebraMap_self_apply,
      SurfaceTarget.splittings, WeightedCurveClass.splittings]
    rw [Finset.sum_image]
    intro c _ d _ he
    exact congrArg Prod.fst he
  | nonseparating x ih =>
    simp only [SurfaceGenusOne.primaryGraphEval, GluingExpression.pointContraction,
      GluingExpression.zeroDecoration, ih hg l, Algebra.algebraMap_self_apply]

end AxiomaticGW.SurfaceGenusTwo

namespace AxiomaticGW.BelorousskiPandharipande

/-- All sixteen lower-genus BP diagrams are undecorated, including both branches
of every node. The four genus-two diagrams are deliberately excluded. -/
theorem lowerTerm_decoration_zero (i : Fin 16) (e : Fin 6) :
    (orbitCotangentTerm (Fin.natAdd 4 i) e).decoration =
      (orbitCotangentTerm (Fin.natAdd 4 i) e).expression.zeroDecoration := by
  change (paperTerm (Fin.natAdd 4 i)).2 = (paperTerm (Fin.natAdd 4 i)).1.zeroDecoration
  fin_cases i <;> (repeat' apply Prod.ext) <;> funext j <;> fin_cases j <;> rfl

/-- Only the sixteen diagrams with lower-genus components contribute to the constant. -/
def lowerPointConstantWithPrimary (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (n : ℕ) (beta : X.Curve) (a : Fin 3 → SurfaceBasisLabel X) : ℚ :=
  ∑ i : Fin 16, rawPaperCoefficient (Fin.natAdd 4 i) * ∑ e,
    let z := orbitCotangentTerm (Fin.natAdd 4 i) e
    z.expression.scalarPointContraction X (SurfaceGenusTwo.primaryConstantPointVertex X v₀ v₁)
      z.decoration z.labels beta n a

/-- Skipping the first four diagrams follows from their retained genus-two component. -/
theorem lowerPointConstantWithPrimary_eq (X : SurfaceTarget) (v₀ v₁ : X.Curve → ℚ)
    (hzero : v₀ = SurfaceGenusZero.pointValue X) (hone : v₁ = SurfaceGenusOne.pointValue X)
    (n : ℕ) (beta : X.Curve) (a : Fin 3 → SurfaceBasisLabel X) :
    lowerPointConstantWithPrimary X v₀ v₁ n beta a = pointConstant X n beta a := by
  have hz (i : Fin 4) (e : Fin 6) :
      2 ≤ (orbitCotangentTerm (Fin.castAdd 16 i) e).expression.maxComponentGenus := by
    fin_cases i <;> exact le_rfl
  simp only [lowerPointConstantWithPrimary, GluingExpression.scalarPointContraction_eq,
    SurfaceGenusTwo.primaryConstantPointVertex_eq X v₀ v₁ hzero hone,
    pointConstant, Fin.sum_univ_add (a := 4) (b := 16),
    SurfaceGenusTwo.point_constant_eq_zero X _ (hz _ _),
    Finset.sum_const_zero, mul_zero, zero_add]

end AxiomaticGW.BelorousskiPandharipande
