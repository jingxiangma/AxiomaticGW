/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoOneMarkingKey
public import AxiomaticGW.Surfaces.GenusTwoAncestorCertificate
public import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate

/-!
# Single-marking descendant transfer in genus two

Moving a cotangent power to the ancestor marking contributes one main
ancestor and a sum over the positive rational tails and the node basis.
A coefficient function may use any proved calibration calculation.
-/

@[expose] public section
namespace AxiomaticGW.SurfaceGenusTwo
open SurfaceDescendant SurfaceGenusTwoBlowupDescendants
variable {X : SurfaceTarget}

/-- The mixed expression for a single mark with remaining descendant power
and accumulated ancestor power. -/
def oneMarkingTerms (cal : ℕ → X.Curve → Matrix (SurfaceBasisLabel X) (SurfaceBasisLabel X) ℚ)
    (beta : X.Curve) (a : SurfaceBasisLabel X) :
    ℕ → ℕ → RationalTerms (SurfaceAncestorKey X)
  | 0, e => RationalTerms.term 1 {oneMarkingKey beta a e}
  | m + 1, e => oneMarkingTerms cal beta a m (e + 1) +
      ∑ split ∈ X.positiveTailSplittings beta, ∑ b : SurfaceBasisLabel X,
        RationalTerms.scale (cal (m+1) split.2 b a)
          (RationalTerms.term 1 {oneMarkingKey split.1 b e})

/-- The original finite transfer at the unique marking has precisely these terms. -/
theorem mixed_oneMarking (beta : X.Curve) (e d : Fin 1 → ℕ) (a : Fin 1 → SurfaceBasisLabel X)
    (h : StableArity 2 (Fin 1)) :
    mixedAncestorTerms 2 (Fin 1) h (List.finRange 1) beta d e a =
      oneMarkingTerms (reconstructedCalibrationMatrix X) beta (a 0) (d 0) (e 0) := by
  change transferMark 0 _ (d 0) beta e a = _
  generalize d 0 = m
  induction m generalizing e with
  | zero =>
    simp only [transferMark, mixedAncestorTerms, oneMarkingTerms, ofLabels_oneMarkingKey]
  | succ m ih =>
    rw [transferMark, oneMarkingTerms, ih]
    simp only [mixedAncestorTerms,
      ofLabels_oneMarkingKey, Function.update_self]

/-- Evaluation of the original ordered singleton query at any canonical table. -/
theorem queryValueWith?_oneMarking (values : SurfaceGenusTwoBlowupOrder.State X → ℚ)
    (beta : X.Curve) (a : SurfaceBasisLabel X) (power : ℕ) :
    queryValueWith? values ⟨2, beta, [⟨a, power⟩]⟩ =
      some (RationalTerms.eval (ancestorValueWith values)
        (oneMarkingTerms (reconstructedCalibrationMatrix X) beta a power 0)) := by
  change some (RationalTerms.eval _
    (mixedAncestorTerms 2 (Fin 1) _ (List.finRange 1) beta _ _ _)) = _
  rw [mixed_oneMarking]
  rfl

open SurfaceGenusTwoBlowupOrder in
/-- A low-psi key whose normalized expression is a single canonical query reads that
entry of the supplied table, including the full curve class and canonical family. -/
theorem ancestorValueWith_of_canonical_singleton (v : State X → ℚ) (q : SurfaceAncestorKey X)
    (beta : X.Curve)
    (f : Family X) (hg : q.genus = 2) (hk : q.totalPsi ≤ 1)
    (ht : SurfacePolynomialReduction.normalizedTerms q =
      RationalTerms.term 1 {Sum.inr (f.query beta)}) :
    ancestorValueWith v q = v (beta, f) := by
  unfold ancestorValueWith
  rw [ancestorValue_low _ q hg hk]
  simp only [SurfaceGenusTwoBlowupLowPsi.ancestorValueWith, ht,
    RationalTerms.eval_term, map_one, Multiset.map_singleton, Multiset.prod_singleton,
    one_mul, canonicalValuation_query]

end AxiomaticGW.SurfaceGenusTwo
