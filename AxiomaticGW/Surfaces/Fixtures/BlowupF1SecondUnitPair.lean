/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoPulledSquare
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveSquareComponents

/-! # The second unit descendant and first exceptional descendant on F₁ -/

@[expose] public section
namespace AxiomaticGW.BlowupF1SecondUnitPair
open SurfaceGenusTwo SurfaceDescendant SurfaceGenusTwoBlowupDescendants
open BlowupF1ExceptionalOneMarkingRequest SurfaceGenusTwoPositiveDivisorPairs

private abbrev X := SurfaceTarget.hirzebruchOne
private abbrev E : SurfaceBasisLabel X := .exceptional 0
private abbrev low := SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary

/-- The complete ordered F₁ request with two positive powers. -/
def request : SurfaceQuery .hirzebruchOne :=
  ⟨2, exceptional, [⟨.unit, 2⟩, ⟨.exceptional 0, 1⟩]⟩

private abbrev high := pairKey exceptional ⟨.unit, 2⟩ ⟨E, 1⟩
private abbrev tailSquare := pairKey (X := X) 0 ⟨.unit, 2⟩ ⟨E, 0⟩
private abbrev tailLow := pairKey (X := X) 0 ⟨E, 0⟩ ⟨E, 1⟩

/-- The old marked point carries the unit. The added point carries E. -/
private def labels : Option (Fin 1) → SurfaceBasisLabel X :=
  fun j ↦ Option.elim j E (fun _ ↦ .unit)

/-- The remaining extra power after removing the square at the old point. -/
private def powers (p : ℕ) : Option (Fin 1) → ℕ := fun j ↦ Option.elim j p (fun _ ↦ 0)

private theorem mixed :
    mixedAncestorTerms 2 (Fin 2) (by norm_num [StableArity]) (List.finRange 2) exceptional
      ![2, 1] 0 ![.unit, E] = RationalTerms.term 1 {high} +
        RationalTerms.term (-1) {tailLow} + RationalTerms.term (-1) {tailSquare} := by
  decide +kernel

private theorem at_square (r : Fin 2) :
    ancestorValue low ((![high, tailSquare] : Fin 2 → SurfaceAncestorKey X) r) =
      pulledSquare (vertex (ancestorValue low)) 1 ((![exceptional, 0] : Fin 2 → X.Curve) r)
        (powers ((![1, 0] : Fin 2 → ℕ) r)) labels := by
  fin_cases r
  all_goals
    rw [ancestorValue_pulledSquare low _ rfl (by decide +kernel) (by decide +kernel), ← vertex_eq]
    congr 1 <;> decide +kernel

private theorem tailLow_zero : low tailLow = 0 := by decide +kernel

/-- Both non-main calibration monomials are attached at class zero. -/
private theorem value_reduction :
    queryValue? 0 request = some (
      pulledSquare (vertex (ancestorValue low)) 1 exceptional (powers 1) labels -
        pulledSquare (vertex (ancestorValue low)) 1 0 (powers 0) labels) := by
  rw [← queryValueWith?_eq_of_table 0 1 boundary boundary_eq_values request (by decide +kernel)]
  change some (RationalTerms.eval (ancestorValueWith boundary)
    (mixedAncestorTerms 2 (Fin 2) _ (List.finRange 2) exceptional _ _ _)) = _
  convert_to some (RationalTerms.eval (ancestorValueWith boundary)
    (mixedAncestorTerms 2 (Fin 2) (by norm_num [StableArity]) (List.finRange 2) exceptional
      ![2, 1] 0 ![.unit, E])) = _ using 1
  · congr 3 <;> funext j <;> fin_cases j <;> rfl
  rw [mixed]
  simp only [RationalTerms.eval_add, RationalTerms.eval_term, Algebra.algebraMap_self_apply,
    Multiset.map_singleton, Multiset.prod_singleton, one_mul, neg_one_mul]
  change some (ancestorValue low high + -ancestorValue low tailLow +
    -ancestorValue low tailSquare) = _
  have main : ancestorValue low high =
      pulledSquare (vertex (ancestorValue low)) 1 exceptional (powers 1) labels := at_square 0
  have tail : ancestorValue low tailSquare =
      pulledSquare (vertex (ancestorValue low)) 1 0 (powers 0) labels := at_square 1
  rw [ancestorValue_low low tailLow rfl (by decide +kernel), tailLow_zero, neg_zero, add_zero,
    main, tail, sub_eq_add_neg]

private def contributions : Fin 2 → Fin 11 → ℚ :=
  ![![0, -155 / 33696, -35 / 16848, -23 / 44928, 0, -7 / 16848, -31 / 5616, -749 / 168480,
      0, -1 / 8320, -1 / 56160],
    ![-1 / 2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
-- The eleven original sources are replayed at the two full curve classes independently.
private theorem source_values (r : Fin 2) (i : Fin 11) :
    pulledSquarePart (SurfaceGenusTwoPositiveSquare.component (ancestorValue low)) 1
      ((![exceptional, 0] : Fin 2 → X.Curve) r) (powers ((![1, 0] : Fin 2 → ℕ) r)) labels i =
        contributions r i := by
  fin_cases r <;> fin_cases i <;> decide +kernel

private theorem squares (r : Fin 2) :
    pulledSquare (vertex (ancestorValue low)) 1 ((![exceptional, 0] : Fin 2 → X.Curve) r)
      (powers ((![1, 0] : Fin 2 → ℕ) r)) labels = (![(-17 / 960), (-1 / 2880)] : Fin 2 → ℚ) r := by
  rw [pulledSquare_eq_parts, ← SurfaceGenusTwoPositiveSquare.component_eq]
  simp only [source_values r]
  fin_cases r <;> decide +kernel

/-- The positive-class and degree-zero squares before their calibration signs. -/
theorem square_values (r : Fin 2) :
    pulledSquare (vertex (ancestorValue (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith boundary))) 1
      ((![exceptional, 0] : Fin 2 → SurfaceTarget.hirzebruchOne.Curve) r)
      (fun x ↦ Option.elim x ((![1, 0] : Fin 2 → ℕ) r) (fun _ ↦ 0))
      (fun x ↦ Option.elim x (.exceptional 0) (fun _ ↦ .unit)) =
      (![(-17 / 960), (-1 / 2880)] : Fin 2 → ℚ) r := squares r

/-- The signed main and class-zero squares give the original mixed descendant value. -/
theorem accepted : queryValue? 0 request = some (-5 / 288) := by
  rw [value_reduction]
  have main : pulledSquare (vertex (ancestorValue low)) 1 exceptional (powers 1) labels =
      -17 / 960 := squares 0
  have tail : pulledSquare (vertex (ancestorValue low)) 1 0 (powers 0) labels =
      -1 / 2880 := squares 1
  rw [main, tail]
  norm_num

end AxiomaticGW.BlowupF1SecondUnitPair
