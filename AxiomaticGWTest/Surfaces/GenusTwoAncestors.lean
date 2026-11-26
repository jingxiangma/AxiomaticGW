import AxiomaticGW.Surfaces.GenusTwoAncestors
import AxiomaticGW.Surfaces.PlaneGenusTwoLowPsi

open AxiomaticGW SurfaceGenusTwo BelorousskiPandharipande

private def key (d : ℕ) (ins : List (SurfaceInsertion .plane)) : SurfaceAncestorKey .plane :=
  ⟨2, ![d], ins, by omega⟩

private def squareQuery : SurfaceAncestorKey .plane :=
  key 1 [⟨.point, 1⟩, ⟨.hyperplane, 3⟩, ⟨.unit, 0⟩]

private def productQuery : SurfaceAncestorKey .plane :=
  key 0 [⟨.hyperplane, 1⟩, ⟨.unit, 1⟩]

private def repeatedQuery : SurfaceAncestorKey .plane :=
  key 0 [⟨.hyperplane, 1⟩, ⟨.hyperplane, 1⟩, ⟨.point, 0⟩]

-- The selector keeps the high power paired with its hyperplane state after sorting.
example : (squareMarks squareQuery).Nonempty := by decide +kernel

example : squareQuery.orderedLabels (squareMark squareQuery (by decide)) = .hyperplane ∧
    squareQuery.orderedPowers (squareMark squareQuery (by decide)) = 3 := by decide +kernel

example : (∑ s, squareLowerPowers squareQuery (by decide) s) = 2 := by decide +kernel

-- Both directions of the two-label frame work when the chosen labels are out of order.
example : ExtraMarkings.twoMarkingFrame 4 (by decide) 3 0 (by decide)
    (ExtraMarkings.oldLabel 2 (0 : Fin 2)) = 3 ∧
    ExtraMarkings.twoMarkingFrame 4 (by decide) 3 0 (by decide)
      (ExtraMarkings.oldLabel 2 (1 : Fin 2)) = 0 := by decide +kernel

example : ExtraMarkings.twoMarkingFrame 2 (by decide) 1 0 (by decide)
    (ExtraMarkings.oldLabel 0 (0 : Fin 2)) = 1 ∧
    ExtraMarkings.twoMarkingFrame 2 (by decide) 1 0 (by decide)
      (ExtraMarkings.oldLabel 0 (1 : Fin 2)) = 0 := by decide +kernel

-- Two identical positive insertions are distinct occurrences, not one square.
example : ¬(squareMarks repeatedQuery).Nonempty := by decide +kernel

example : firstProductMark repeatedQuery (by decide) ≠
    secondProductMark repeatedQuery (by decide) (by decide) := by decide +kernel

example : (∑ s, productLowerPowers repeatedQuery (by decide) (by decide) s) = 0 := by
  decide +kernel

-- Fuel independence and strict descent apply to every full class on all three targets.
example {X : SurfaceTarget} (base : SurfaceAncestorKey X → ℚ) (q : SurfaceAncestorKey X)
    (hg : q.genus = 2) : ancestorValueFuel base (q.totalPsi + 5) q = ancestorValue base q :=
  ancestorValueFuel_stable base _ _ q hg (by omega) le_rfl

example {X : SurfaceTarget} (q : SurfaceAncestorKey X) (hk : 1 < q.totalPsi)
    (t : ℚ × Multiset (SurfaceAncestorKey X)) (ht : t ∈ ancestorReductionTerms q hk)
    (r : SurfaceAncestorKey X) (hr : r ∈ t.2) :
    r.genus = 2 ∧ r.totalPsi < q.totalPsi := by
  have hb := ancestorReductionTerms_dependency q hk ht r hr
  exact ⟨hb.1, hb.2.2.1⟩

-- The executable recursion reduces a two-descendant query to the certified initial triple.
-- This is an algorithm regression; the final all-input geometric consumer remains separate.
set_option maxRecDepth 20000 in
example : ancestorValue (planeLowPsiValueWith (fun _ ↦ ![0, -1 / 960, 0])) productQuery =
    -1 / 320 := by decide +kernel
