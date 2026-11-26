/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPrimaryConstant

/-!
# Primary evaluation of the lower-genus BP constant

Each of the sixteen lower-genus diagrams is undecorated. The primary evaluator
therefore preserves each diagram and its raw coefficient. Equal external labels
give identical evaluations at all six ordered assignments.
-/

@[expose] public section
namespace AxiomaticGW.BelorousskiPandharipande

/-- The complete constant with its original six forward marking assignments. -/
theorem lowerPointConstantWithPrimary_eq_primaryGraphSum (X : SurfaceTarget)
    (v₀ v₁ : X.Curve → ℚ) (n : ℕ) (beta : X.Curve) (a : Fin 3 → SurfaceBasisLabel X) :
    lowerPointConstantWithPrimary X v₀ v₁ n beta a =
      ∑ i : Fin 16, rawPaperCoefficient (Fin.natAdd 4 i) * ∑ e : Fin 6,
        SurfaceGenusOne.primaryGraphDimensionEval X v₀ v₁ (paperTerm (Fin.natAdd 4 i)).1
          beta n (a ∘ labelPermutation e) := by
  simp only [SurfaceGenusOne.primaryGraphDimensionEval_eq]
  unfold lowerPointConstantWithPrimary
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  have hg : (orbitCotangentTerm (Fin.natAdd 4 i) e).expression.maxComponentGenus ≤ 1 := by
    change (paperTerm (Fin.natAdd 4 i)).1.maxComponentGenus ≤ 1
    exact paperTerm_lower_genus _ (by change 4 ≤ 4 + i.val; omega)
  rw [GluingExpression.scalarPointContraction_eq, lowerTerm_decoration_zero,
    ← SurfaceGenusTwo.primaryGraphEval_pointContraction_eq X v₀ v₁ _ hg]
  rfl

/-- All six ordered assignments contribute for three equal external labels. -/
theorem lowerPointConstantWithPrimary_eq_six_primaryGraphSum (X : SurfaceTarget)
    (v₀ v₁ : X.Curve → ℚ) (n : ℕ) (beta : X.Curve) (a : SurfaceBasisLabel X) :
    lowerPointConstantWithPrimary X v₀ v₁ n beta (fun _ ↦ a) =
      6 * ∑ i : Fin 16, rawPaperCoefficient (Fin.natAdd 4 i) *
        SurfaceGenusOne.primaryGraphDimensionEval X v₀ v₁ (paperTerm (Fin.natAdd 4 i)).1
          beta n (fun _ ↦ a) := by
  rw [lowerPointConstantWithPrimary_eq_primaryGraphSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end AxiomaticGW.BelorousskiPandharipande
