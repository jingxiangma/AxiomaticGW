/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoBlowupRecursion
public import AxiomaticGW.Surfaces.GenusTwoL24ConstantGuard
public import AxiomaticGW.Surfaces.GenusTwoCoefficientRelations
public import AxiomaticGW.Coefficients.AffineEvaluation

/-!
# Exact scalar replay for the selected genus-two blowup rows

The scalar constant and each compressed singleton coefficient are bound to the
unchanged H/P/N/K equation selected by the reconstruction. The H and N rows
retain their exceptional source shift; all point counts, signs and four-row N
weights are unchanged, including at class zero and negative signed multiplicity.
The H constant skips only terms proved zero by the higher-genus L24 guard;
its scalar equality retains the complete original equation.

A supplied finite list of canonical states gives exact row evaluation once it
covers the variables in the collected row. Repeated states are deduplicated by
their full queries. Coverage is a finite support condition, not a row-vanishing
or recurrence assumption. No numerical values or geometric inputs are added.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwoBlowupScalar
open SurfacePolynomialReduction SurfaceGenusTwoBlowupOrder
variable {X : SurfaceTarget}

-- The H equation uses the unchanged 815-column L24 source dispatch.
set_option maxRecDepth 20000

/-- The exact lower-genus constant of the selected row, retaining full source classes. -/
def constant (i : Fin X.blowups) (s : State X) : ℚ :=
  match s.2 with
  | .hyperplane => L24Relation.pointConstantGuarded X (X.effective.energy s.1 - 1)
      (s.1 + X.exceptionalCurve i) ![.hyperplane, .exceptional i, .exceptional i, .exceptional i]
  | .point => BelorousskiPandharipande.pointConstant X (X.effective.energy s.1 - 1) s.1
      ![.hyperplane, .hyperplane, .hyperplane]
  | .primary =>
      (3 * (X.planeDegree s.1 : ℚ) / 2) * BelorousskiPandharipande.pointConstant X
        (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
        ![.exceptional i, .hyperplane, .hyperplane] +
      (-1) * BelorousskiPandharipande.pointConstant X (X.effective.energy s.1)
        (s.1 + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .hyperplane] +
      ((X.planeDegree s.1 : ℚ) / 2) * BelorousskiPandharipande.pointConstant X
        (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
        ![.exceptional i, .exceptional i, .exceptional i] +
      (-1 / 3) * BelorousskiPandharipande.pointConstant X (X.effective.energy s.1)
        (s.1 + X.exceptionalCurve i) ![.hyperplane, .hyperplane, .hyperplane]
  | .exceptional j => BelorousskiPandharipande.pointConstant X (X.effective.energy s.1 - 1)
      s.1 ![.exceptional j, .exceptional j, .exceptional j]

/-- Compression gives the exact coefficient of any singleton in the selected full row. -/
def singletonCoefficient (i : Fin X.blowups) (s : State X) (v : Variable X) : ℚ :=
  match s.2 with
  | .hyperplane => L24Relation.pointCoefficient X (X.effective.energy s.1 - 1)
      (s.1 + X.exceptionalCurve i) ![.hyperplane, .exceptional i, .exceptional i, .exceptional i] v
  | .point => BelorousskiPandharipande.pointCoefficient X (X.effective.energy s.1 - 1) s.1
      ![.hyperplane, .hyperplane, .hyperplane] v
  | .primary =>
      (3 * (X.planeDegree s.1 : ℚ) / 2) * BelorousskiPandharipande.pointCoefficient X
        (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
        ![.exceptional i, .hyperplane, .hyperplane] v +
      (-1) * BelorousskiPandharipande.pointCoefficient X (X.effective.energy s.1)
        (s.1 + X.exceptionalCurve i) ![.exceptional i, .exceptional i, .hyperplane] v +
      ((X.planeDegree s.1 : ℚ) / 2) * BelorousskiPandharipande.pointCoefficient X
        (X.effective.energy s.1) (s.1 + X.exceptionalCurve i)
        ![.exceptional i, .exceptional i, .exceptional i] v +
      (-1 / 3) * BelorousskiPandharipande.pointCoefficient X (X.effective.energy s.1)
        (s.1 + X.exceptionalCurve i) ![.hyperplane, .hyperplane, .hyperplane] v
  | .exceptional j => BelorousskiPandharipande.pointCoefficient X (X.effective.energy s.1 - 1)
      s.1 ![.exceptional j, .exceptional j, .exceptional j] v

/-- The scalar constant is the zero valuation of the entire selected normalized equation. -/
theorem constant_eq (i : Fin X.blowups) (s : State X) :
    constant i s = RationalTerms.eval (fun _ ↦ (0 : ℚ))
      (SurfaceGenusTwoBlowupRecursion.row i s) := by
  obtain ⟨beta, family⟩ := s
  cases family with
  | hyperplane => exact L24Relation.pointConstantGuarded_eq_normalized X _ _ _
  | point => exact BelorousskiPandharipande.pointConstant_eq_normalized X _ _ _
  | primary =>
      simp only [constant, SurfaceGenusTwoBlowupRecursion.row,
        SurfaceGenusTwoBlowupNRelation.row, SurfaceGenusTwoBlowupNRelation.bpRow,
        RationalTerms.eval_add, RationalTerms.eval_scale, Algebra.algebraMap_self_apply,
        ← BelorousskiPandharipande.pointConstant_eq_normalized]
  | exceptional j => exact BelorousskiPandharipande.pointConstant_eq_normalized X _ _ _

/-- Every compressed coefficient belongs to the actual row at the exact requested variable. -/
theorem singletonCoefficient_eq (i : Fin X.blowups) (s : State X) (v : Variable X) :
    singletonCoefficient i s v =
      RationalTerms.coefficient (SurfaceGenusTwoBlowupRecursion.row i s) {v} := by
  obtain ⟨beta, family⟩ := s
  cases family with
  | hyperplane => exact L24Relation.pointCoefficient_eq_full X _ _ _ v
  | point => exact BelorousskiPandharipande.pointCoefficient_eq_full X _ _ _ v
  | primary =>
      simp only [singletonCoefficient, SurfaceGenusTwoBlowupRecursion.row,
        SurfaceGenusTwoBlowupNRelation.row, SurfaceGenusTwoBlowupNRelation.bpRow,
        RationalTerms.coefficient_add, RationalTerms.coefficient_scale,
        ← BelorousskiPandharipande.pointCoefficient_eq_full]
  | exceptional j => exact BelorousskiPandharipande.pointCoefficient_eq_full X _ _ _ v

/-- A finite list is deduplicated by exact full query equality, retaining exceptional labels. -/
def columns (states : List (State X)) : Finset (Variable X) :=
  (states.map (fun s ↦ Sum.inr (s.2.query s.1))).toFinset

/-- Column membership asserts equality of the whole canonical state query. -/
theorem mem_columns (states : List (State X)) (v : Variable X) :
    v ∈ columns states ↔ ∃ s ∈ states, v = Sum.inr (s.2.query s.1) := by
  simp only [columns, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

/-- Collection leaves only constant or singleton terms in every selected row. -/
theorem collected_row_affine (i : Fin X.blowups) (s : State X)
    {t : ℚ × Multiset (Variable X)}
    (ht : t ∈ RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)) :
    t.2 = 0 ∨ ∃ v : Variable X, t.2 = {v} := by
  obtain ⟨beta, family⟩ := s
  cases family with
  | hyperplane =>
      rcases L24Relation.collected_normalized_primary_canonical_support
        (X.effective.energy beta - 1) (beta + X.exceptionalCurve i) _ ht with
        hz | ⟨gamma, c, _, hm, _⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Sum.inr c, hm⟩
  | point =>
      rcases BelorousskiPandharipande.collected_normalized_primary_canonical_support
        (X.effective.energy beta - 1) beta _ ht with hz | ⟨gamma, c, _, hm, _⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Sum.inr c, hm⟩
  | primary =>
      rcases SurfaceGenusTwoBlowupNRelation.collected_row_canonical_support i beta ht with
        hz | ⟨gamma, c, _, hm, _⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Sum.inr c, hm⟩
  | exceptional j =>
      rcases BelorousskiPandharipande.collected_normalized_primary_canonical_support
        (X.effective.energy beta - 1) beta _ ht with hz | ⟨gamma, c, _, hm, _⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Sum.inr c, hm⟩

/-- Replay one constant and the exact finite singleton columns. A zero value skips
its coefficient computation without removing any nonzero polynomial term. -/
def replay (i : Fin X.blowups) (s : State X) (values : Variable X → ℚ)
    (states : List (State X)) : ℚ :=
  constant i s + ∑ v ∈ columns states,
    if values v = 0 then 0 else singletonCoefficient i s v * values v

/-- Finite coverage of the collected row suffices for exact scalar evaluation.
This premise checks full queries and cancellation; it assumes no numerical equation. -/
theorem replay_eq_row (i : Fin X.blowups) (s : State X) (values : Variable X → ℚ)
    (states : List (State X))
    (hcover : ∀ v ∈ (RationalTerms.collect
      (SurfaceGenusTwoBlowupRecursion.row i s)).bind Prod.snd, v ∈ columns states) :
    replay i s values states = RationalTerms.eval values
      (SurfaceGenusTwoBlowupRecursion.row i s) := by
  have hs : ∀ t ∈ RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s),
      t.2 = 0 ∨ ∃ v ∈ columns states, t.2 = {v} := by
    intro t ht
    rcases collected_row_affine i s ht with hz | ⟨v, hm⟩
    · exact Or.inl hz
    · refine Or.inr ⟨v, hcover v ?_, hm⟩
      apply Multiset.mem_bind.mpr
      refine ⟨t, ht, ?_⟩
      rw [hm]
      exact Multiset.mem_singleton_self v
  have he := RationalTerms.eval_eq_constant_add_sum values
    (RationalTerms.collect (SurfaceGenusTwoBlowupRecursion.row i s)) (columns states) hs
  rw [RationalTerms.eval_collect, RationalTerms.eval_collect] at he
  simp only [RationalTerms.coefficient_collect] at he
  have hz (c x : ℚ) : (if x = 0 then 0 else c * x) = c * x := by
    by_cases hx : x = 0
    · rw [if_pos hx, hx, mul_zero]
    · exact if_neg hx
  simpa only [replay, constant_eq, singletonCoefficient_eq, hz] using he.symm

end AxiomaticGW.SurfaceGenusTwoBlowupScalar
