/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.FirstDescendantReduction

/-! # Genus-two string and dilaton equations with one other marking

At two markings the string sum has a single summand, and the dilaton multiplier is
2g − 2 + 1 = 3. Both orders of the original query retain the complete curve class.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- The two forgetful equations that remove a unit from a stable-map descendant. -/
inductive UnitEquation | string | dilaton
  deriving DecidableEq, Repr, Fintype

/-- The scalar for a positive-power string summand or the genus-two dilaton equation. -/
def UnitEquation.factor : UnitEquation → ℚ | .string => 1 | .dilaton => 3

/-- Insert a unit in either order, incrementing the other cotangent power for string. -/
def UnitEquation.pair (rule : UnitEquation) (unitLast : Bool) (beta : X.Curve)
    (s : SurfaceInsertion X) : SurfaceQuery X :=
  let (u, t) : SurfaceInsertion X × SurfaceInsertion X := match rule with
    | .string => (⟨.unit, 0⟩, ⟨s.label, s.psi + 1⟩)
    | .dilaton => (⟨.unit, 1⟩, s)
  ⟨2, beta, if unitLast then [t, u] else [u, t]⟩

variable {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}

/-- Reindex either ordered pair by an optional singleton, placing the selected mark at none. -/
theorem eval_ordered_pair (U : UnstableDescendantConventions M I) (last : Bool)
    (beta : X.Curve) (u t : SurfaceInsertion X) :
    SurfaceQuery.eval U ⟨2, beta, if last then [t, u] else [u, t]⟩ =
      U.invariant 2 (Option (Fin 1)) beta
        (fun | none => u.psi | some _ => t.psi)
        (fun | none => u.label.value | some _ => t.label.value) := by
  cases last
  · change U.invariant 2 (Fin 2) beta (fun i ↦ ([u, t].get i).psi)
      (fun i ↦ ([u, t].get i).label.value) = _
    rw [SurfaceFirstDescendant.invariant_relabel U 2 beta (Fin 2) _ (finSuccEquiv 1)]
    congr 1 <;> funext i <;> (cases i with
      | none => rfl
      | some i => fin_cases i; rfl)
  · change U.invariant 2 (Fin 2) beta (fun i ↦ ([t, u].get i).psi)
      (fun i ↦ ([t, u].get i).label.value) = _
    rw [SurfaceFirstDescendant.invariant_relabel U 2 beta (Fin 2) _
      ((Equiv.swap 0 1).trans (finSuccEquiv 1))]
    congr 1 <;> funext i <;> (cases i with
      | none => rfl
      | some i => fin_cases i; rfl)

/-- Evaluation in the singleton frame has constant state and power. -/
theorem eval_singleton_marking (U : UnstableDescendantConventions M I)
    (beta : X.Curve) (s : SurfaceInsertion X) :
    SurfaceQuery.eval U ⟨2, beta, [s]⟩ =
      U.invariant 2 (Fin 1) beta (fun _ ↦ s.psi) (fun _ ↦ s.label.value) := by
  simp only [SurfaceQuery.eval, List.length_singleton, List.get_eq_getElem, List.getElem_singleton]

/-- The exact two-marked geometric descendant follows from its singleton. Only the unit
identification and the stable string/dilaton laws are used. -/
theorem UnitEquation.eval_pair (U : UnstableDescendantConventions M I)
    (hu : Omega.unit = 1) (laws : DescendantStringDilatonLaws M I)
    (rule : UnitEquation) (last : Bool) (beta : X.Curve) (s : SurfaceInsertion X) :
    (rule.pair last beta s).eval U = rule.factor * SurfaceQuery.eval U ⟨2, beta, [s]⟩ := by
  have stable : StableArity 2 (Fin 1) := by simp only [StableArity, Fintype.card_fin]; decide
  cases rule with
  | string =>
    rw [UnitEquation.pair, eval_ordered_pair, UnitEquation.factor, one_mul, eval_singleton_marking]
    have h := U.global_string laws 2 (Fin 1) beta (fun _ ↦ s.psi + 1) (fun _ ↦ s.label.value)
    rw [stringCorrection_eq_zero_of_stable _ _ _ _ _ _ stable, add_zero, Fintype.sum_unique,
      if_neg (Nat.succ_ne_zero _), hu] at h
    have hk : lowerPower (fun _ : Fin 1 ↦ s.psi + 1) default = fun _ ↦ s.psi := by
      funext i
      rw [Subsingleton.elim i default, lowerPower, Function.update_self, Nat.add_sub_cancel]
    rw [hk] at h
    convert! h using 1
    congr 1 <;> funext i <;> cases i <;> rfl
  | dilaton =>
    rw [UnitEquation.pair, eval_ordered_pair, UnitEquation.factor, eval_singleton_marking]
    have h := U.global_dilaton laws 2 (Fin 1) beta (fun _ ↦ s.psi) (fun _ ↦ s.label.value)
    rw [dilatonCorrection_eq_zero_of_stable _ _ _ _ stable, add_zero, hu] at h
    rw [show dilatonCoefficient ℚ 2 (Fin 1) = 3 by decide +kernel] at h
    convert! h using 1
    congr 1 <;> funext i <;> cases i <;> rfl

/-- If the surviving insertion is primary, the string sum has no positive power to lower.
This also covers the two-primary boundary case of the two-marked string equation. -/
theorem eval_primary_unit_pair (U : UnstableDescendantConventions M I)
    (hu : Omega.unit = 1) (laws : DescendantStringDilatonLaws M I)
    (last : Bool) (beta : X.Curve) (a : SurfaceBasisLabel X) :
    SurfaceQuery.eval U ⟨2, beta,
      if last then [⟨a, 0⟩, ⟨.unit, 0⟩] else [⟨.unit, 0⟩, ⟨a, 0⟩]⟩ = 0 := by
  rw [eval_ordered_pair U last beta ⟨.unit, 0⟩ ⟨a, 0⟩]
  have stable : StableArity 2 (Fin 1) := by simp only [StableArity, Fintype.card_fin]; decide
  have h := U.global_string laws 2 (Fin 1) beta (fun _ ↦ 0) (fun _ ↦ a.value)
  rw [stringCorrection_eq_zero_of_stable _ _ _ _ _ _ stable, add_zero, Fintype.sum_unique,
    if_pos rfl, hu] at h
  convert! h using 1
  congr 1 <;> funext i <;> cases i <;> rfl

end AxiomaticGW.SurfaceGenusTwo
