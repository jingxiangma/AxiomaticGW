/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoOneMarkingTransfer
public import AxiomaticGW.Surfaces.GenusTwoAncestorCertificate

/-!
# One-marking descendant transfer at an exceptional curve

For a primitive exceptional class, a nonzero tail carries the whole curve.
Through the dimension-compatible third cotangent power, the only remaining
main-curve insertions are a class-zero point or a first ancestor of the
exceptional divisor carrying that curve.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceDescendant SurfaceGenusTwoBlowupOrder SurfaceGenusTwoBlowupDescendants

variable {X : SurfaceTarget}

private def exceptionalTails (i : Fin X.blowups) (a : SurfaceBasisLabel X) :
    RationalTerms (SurfaceAncestorKey X) :=
  let divisor := RationalTerms.term (-1) {oneMarkingKey 0 (.exceptional i) 1}
  let point (c : ℚ) := RationalTerms.term c {oneMarkingKey (X := X) 0 .point 0}
  if a = .unit then divisor + point (-2) else
  if a = .exceptional i then divisor + point (-1) else 0

private theorem exceptional_terms (i : Fin X.blowups) (a : SurfaceBasisLabel X) :
    oneMarkingTerms (reconstructedCalibrationMatrix X) (X.exceptionalCurve i) a
      (3 - a.codimension) 0 =
    RationalTerms.term 1 {oneMarkingKey (X.exceptionalCurve i) a (3 - a.codimension)} +
      exceptionalTails i a := by
  revert i a
  cases X <;> decide +kernel

private theorem point_normalized (i : Fin X.blowups) :
    SurfacePolynomialReduction.normalizedTerms (oneMarkingKey (X.exceptionalCurve i) .point 1) =
      RationalTerms.term 1 {Sum.inr (Family.point.query (X.exceptionalCurve i))} := by
  cases X <;> fin_cases i <;> decide +kernel

private theorem divisor_zero_normalized (i : Fin X.blowups) :
    SurfacePolynomialReduction.normalizedTerms (oneMarkingKey (X := X) 0 (.exceptional i) 1) =
      RationalTerms.term 1 {Sum.inr ((Family.exceptional i).query 0)} := by
  cases X <;> fin_cases i <;> decide +kernel

private theorem point_zero_normalized (X : SurfaceTarget) :
    SurfacePolynomialReduction.normalizedTerms (oneMarkingKey (X := X) 0 .point 0) =
      RationalTerms.term 1 {Sum.inr ((Family.primary (X := X)).query 0)} := by
  cases X <;> decide +kernel

private theorem eval_singleton (v : SurfaceAncestorKey X → ℚ)
    (c : ℚ) (q : SurfaceAncestorKey X) :
    RationalTerms.eval v (RationalTerms.term c {q}) = c * v q := by
  simp only [RationalTerms.eval_term, RingHom.id_apply, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self]

/-- The point descendant at a primitive exceptional curve reads its canonical
point state at the same full class. -/
theorem queryValueWith?_exceptional_point (v : State X → ℚ) (i : Fin X.blowups) :
    queryValueWith? v ⟨2, X.exceptionalCurve i, [⟨.point, 1⟩]⟩ =
      some (v (X.exceptionalCurve i, .point)) := by
  have ht := exceptional_terms i .point
  rw [queryValueWith?_oneMarking]
  change oneMarkingTerms (reconstructedCalibrationMatrix X) (X.exceptionalCurve i) .point 1 0 =
      RationalTerms.term 1 {oneMarkingKey (X.exceptionalCurve i) .point 1} + 0 at ht
  rw [ht, add_zero, eval_singleton, one_mul]
  exact congrArg some (ancestorValueWith_of_canonical_singleton v _ _ _ rfl
    (by change 1 ≤ 1; decide) (point_normalized i))

/-- The full mixed descendant at virtual dimension equals its single ancestor
plus the signed class-zero point and exceptional-divisor corrections. -/
theorem queryValueWith?_exceptional (v : State X → ℚ) (i : Fin X.blowups)
    (a : SurfaceBasisLabel X) :
    queryValueWith? v ⟨2, X.exceptionalCurve i, [⟨a, 3 - a.codimension⟩]⟩ =
      some (ancestorValueWith v (oneMarkingKey (X.exceptionalCurve i) a (3 - a.codimension)) +
        if a = .unit then -v (0, .exceptional i) - 2 * v (0, .primary)
        else if a = .exceptional i then -v (0, .exceptional i) - v (0, .primary) else 0) := by
  have he := ancestorValueWith_of_canonical_singleton v _ _ _ rfl
    (by change 1 ≤ 1; decide) (divisor_zero_normalized i)
  have hp := ancestorValueWith_of_canonical_singleton v _ _ _ rfl
    (by change 0 ≤ 1; decide) (point_zero_normalized X)
  rw [queryValueWith?_oneMarking, exceptional_terms, RationalTerms.eval_add,
    eval_singleton, one_mul]
  unfold exceptionalTails
  split_ifs <;> simp only [RationalTerms.eval_zero, RationalTerms.eval_add, eval_singleton, he, hp]
  all_goals (congr 2; ring)

end AxiomaticGW.SurfaceGenusTwo
