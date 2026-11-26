/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.GluingForgetful

/-!
# The primitive rational tail for a forgetful map

These are the original labels, raw gluing expression and boundary identification
used by `PsiBoundaryExpansion`. They are shared here without a dependency on
low-genus relation certificates. Declaration names and statements are unchanged.
-/

@[expose] public section

namespace AxiomaticGW.PsiBoundaryExpansion

/-- The surviving main labels, the old marked label, and the new marking. -/
def tailLabels {S : Type} [DecidableEq S] (s : S) : {t : S // t ≠ s} ⊕ Bool ≃ Option S where
  toFun
    | .inl t => some t.val
    | .inr false => some s
    | .inr true => none
  invFun
    | none => .inr true
    | some t => if ht : t = s then .inr false else .inl ⟨t, ht⟩
  left_inv := by
    intro x
    rcases x with t | b
    · simp only [dif_neg t.property]
    · cases b <;> simp only [↓reduceDIte]
  right_inv := by
    intro x
    cases x with
    | none => rfl
    | some t =>
      by_cases h : t = s
      · subst t
        simp only [↓reduceDIte]
      · simp only [dif_neg h]

/-- Raw divisor where the retained label and the new label lie on a rational tail. -/
def tailExpression (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) : GluingExpression g (Option S) :=
  (((GluingExpression.fundamental g S h).relabel (Equiv.optionSubtypeNe s).symm).separating
    (GluingExpression.fundamental 0 (Option Bool) (by norm_num [StableArity]))).relabel
      (tailLabels s)

/-- Every primitive tail has exactly one separating node. -/
theorem tailExpression_edgeCount (g : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) : (tailExpression g S h s).graph.graph.edgeCount = 1 := rfl

/-- The original marking becomes the attaching flag of the main component. -/
theorem tailMainStable {g : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (h : StableArity g S) (s : S) : StableArity g (Option {t : S // t ≠ s}) :=
  (StableArity.equiv (Equiv.optionSubtypeNe s).symm).mp h

/-- The tail has its node, retained marking and new marking. -/
theorem tailStable : StableArity 0 (Option Bool) := by norm_num [StableArity]

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}

/-- The primitive boundary term is its actual raw gluing class. -/
def TailCompatible {P : PsiClasses C} (K : PsiForgetFormula P)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) : Prop :=
  ∀ (g : ℕ) (S : Type) [Fintype S] [DecidableEq S] (h : StableArity g S) (s : S),
    K.boundaryTail g S h s = (tailExpression g S h s).classValue F N

end AxiomaticGW.PsiBoundaryExpansion
