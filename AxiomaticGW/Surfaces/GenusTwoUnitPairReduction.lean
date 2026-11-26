/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoUnitPairs
public import AxiomaticGW.Surfaces.GenusTwoBlowupDescendants

/-! # Checked reduction of ordered genus-two unit pairs to the blowup singleton evaluator -/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
variable {X : SurfaceTarget}

/-- Read the string or dilaton insertion in the first slot. -/
def UnitEquation.removeFront? (u t : SurfaceInsertion X) :
    Option (UnitEquation × SurfaceInsertion X) :=
  match u.label, u.psi, t.psi with
  | .unit, 0, k + 1 => some (.string, ⟨t.label, k⟩)
  | .unit, 1, _ => some (.dilaton, t)
  | _, _, _ => none

/-- Extract a positive-power string summand or a dilaton singleton, searching both orders. -/
def unitPairReduction? (q : SurfaceQuery X) : Option (UnitEquation × SurfaceInsertion X) :=
  match q with
  | ⟨2, _, [u, t]⟩ => UnitEquation.removeFront? u t <|> UnitEquation.removeFront? t u
  | _ => none

private theorem UnitEquation.removeFront?_sound (beta : X.Curve) (u t : SurfaceInsertion X)
    {rule : UnitEquation} {s : SurfaceInsertion X}
    (h : UnitEquation.removeFront? u t = some (rule, s)) :
    rule.pair false beta s = ⟨2, beta, [u, t]⟩ ∧
    rule.pair true beta s = ⟨2, beta, [t, u]⟩ := by
  rcases u with ⟨a, p⟩
  rcases t with ⟨b, k⟩
  cases a <;> rcases p with _ | ⟨_ | p⟩ <;> cases k <;>
    simp only [UnitEquation.removeFront?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    rcases h with ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- Every recognized query is exactly the ordered pair of its reported singleton and unit. -/
theorem unitPairReduction?_sound (q : SurfaceQuery X) {rule : UnitEquation} {s : SurfaceInsertion X}
    (h : unitPairReduction? q = some (rule, s)) :
    ∃ last, q = rule.pair last q.beta s := by
  unfold unitPairReduction? at h
  split at h
  · rename_i beta u t
    cases h₁ : UnitEquation.removeFront? u t with
    | none =>
      rw [h₁] at h
      exact ⟨true, (UnitEquation.removeFront?_sound beta t u h).2.symm⟩
    | some v =>
      rw [h₁] at h
      obtain rfl := Option.some.inj (show some v = some (rule, s) from h)
      exact ⟨false, (UnitEquation.removeFront?_sound beta u t h₁).1.symm⟩
  · contradiction

/-- Evaluate only when the original ordered two-marking query admits the specified reduction. -/
def unitPairValue? (i : Fin X.blowups) (q : SurfaceQuery X) : Option ℚ :=
  match unitPairReduction? q with
  | none => none
  | some (rule, s) => (SurfaceGenusTwoBlowupDescendants.queryValue? i ⟨2, q.beta, [s]⟩).map
      (rule.factor * ·)

/-- Successful evaluation exhibits the specific recognized equation and surviving insertion. -/
theorem exists_reduction_of_unitPairValue? (i : Fin X.blowups) (q : SurfaceQuery X) {v : ℚ}
    (hv : unitPairValue? i q = some v) :
    ∃ rule s, unitPairReduction? q = some (rule, s) := by
  cases h : unitPairReduction? q with
  | none => simp only [unitPairValue?, h, reduceCtorEq] at hv
  | some p => exact ⟨p.1, p.2, rfl⟩

/-- The original finite evaluator and the shortcut agree whenever geometric reconstruction
identifies its queries. The original-equations specialization supplies this identification. -/
theorem unitPairValue?_eq_of_identification {C : StableCurveCohomology ℚ}
    {Omega : GromovWittenTheory ℚ (SurfaceCohomology X.blowups) X.Curve X.effective C}
    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}
    (U : UnstableDescendantConventions M I) (hu : Omega.unit = 1)
    (laws : DescendantStringDilatonLaws M I) (i : Fin X.blowups)
    (hid : ∀ q : SurfaceQuery X, q.genus = 2 →
      SurfaceGenusTwoBlowupDescendants.queryValue? i q = q.checkedEval U)
    (q : SurfaceQuery X) {rule : UnitEquation} {s : SurfaceInsertion X}
    (h : unitPairReduction? q = some (rule, s)) :
    SurfaceGenusTwoBlowupDescendants.queryValue? i q = unitPairValue? i q := by
  obtain ⟨last, hq⟩ := unitPairReduction?_sound q h
  have hg := congrArg SurfaceQuery.genus hq
  change q.genus = 2 at hg
  have hd (r : SurfaceQuery X) (hr : r.genus = 2) : r.GeometricDomain :=
    Or.inr (by simp only [StableArity, hr]; omega)
  rw [unitPairValue?, h, hid q hg, SurfaceQuery.checkedEval_of_geometricDomain U q (hd q hg)]
  change some (q.eval U) = (SurfaceGenusTwoBlowupDescendants.queryValue? i ⟨2, q.beta, [s]⟩).map _
  rw [hid _ rfl, SurfaceQuery.checkedEval_of_geometricDomain U _ (hd _ rfl)]
  change some (q.eval U) = some (rule.factor * SurfaceQuery.eval U ⟨2, q.beta, [s]⟩)
  exact congrArg some ((congrArg (SurfaceQuery.eval U) hq).trans (rule.eval_pair U hu laws _ _ _))

end AxiomaticGW.SurfaceGenusTwo
