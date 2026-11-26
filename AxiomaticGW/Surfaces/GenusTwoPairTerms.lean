/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate
public import AxiomaticGW.Surfaces.GenusTwoPrimitivePairTransfer

/-! # Exact tables for the ordered two-marked descendant transfer -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceDescendant SurfaceGenusTwoBlowupDescendants
variable {X : SurfaceTarget}

/-- Keep both occurrences in the ordered mixed transfer. -/
def pairMixed (beta : X.Curve) (a b : SurfaceInsertion X) :
    RationalTerms (SurfaceAncestorKey X) :=
  mixedAncestorTerms 2 (Fin 2) (by norm_num [StableArity]) (List.finRange 2) beta
    ![a.psi, b.psi] 0 ![a.label, b.label]

theorem queryValueWith?_pair (v : SurfaceGenusTwoBlowupOrder.State X → ℚ)
    (beta : X.Curve) (a b : SurfaceInsertion X) :
    queryValueWith? v ⟨2, beta, [a, b]⟩ =
      some (RationalTerms.eval (ancestorValueWith v) (pairMixed beta a b)) := by
  change some (RationalTerms.eval (ancestorValueWith v)
    (mixedAncestorTerms 2 (Fin 2) _ (List.finRange 2) beta _ _ _)) = _
  unfold pairMixed
  congr 3 <;> funext j <;> fin_cases j <;> rfl

/-- A sparse list of linear monomials in ancestor keys. Occurrences with equal keys are retained. -/
def pairExpression {n : ℕ} (key : Fin n → SurfaceAncestorKey X) (row : List (ℚ × Fin n)) :
    RationalTerms (SurfaceAncestorKey X) :=
  (row.map fun t ↦ RationalTerms.term t.1 {key t.2}).sum

theorem eval_pairExpression {n : ℕ} (key : Fin n → SurfaceAncestorKey X)
    (f : SurfaceAncestorKey X → ℚ) (row : List (ℚ × Fin n)) :
    RationalTerms.eval f (pairExpression key row) =
      (row.map fun t ↦ t.1 * f (key t.2)).sum := by
  induction row with
  | nil => simp only [pairExpression, List.map_nil, List.sum_nil, RationalTerms.eval_zero]
  | cons t rest ih =>
    simp only [pairExpression, List.map_cons, List.sum_cons, RationalTerms.eval_add,
      RationalTerms.eval_term, Algebra.algebraMap_self_apply, Multiset.map_singleton,
      Multiset.prod_singleton] at ih ⊢
    rw [ih]

end AxiomaticGW.SurfaceGenusTwo
