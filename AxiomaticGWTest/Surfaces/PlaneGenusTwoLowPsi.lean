import AxiomaticGW.Surfaces.PlaneGenusTwoLowPsi

open AxiomaticGW BelorousskiPandharipande

private def key (d : ℕ) (ins : List (SurfaceInsertion .plane)) : SurfaceAncestorKey .plane :=
  ⟨2, ![d], ins, by omega⟩

private def initialTable : ℕ → Fin 3 → ℚ := fun _ ↦ ![0, -1 / 960, 0]

private theorem initial_checked : planeCheckCanonicalTable 0 initialTable = true := by
  decide +kernel

-- The empty genus-two marking set is stable; dimension filtering makes this primary zero.
example : planeLowPsiValueWith initialTable (key 0 []) = 0 := by decide +kernel

-- Degree zero retains the nonzero first hyperplane value and the dimension-forced point zero.
example : planeLowPsiValueWith initialTable (key 0 [⟨.hyperplane, 1⟩]) = -1 / 960 := by
  decide +kernel

example : planeLowPsiValueWith initialTable (key 0 [⟨.point, 1⟩]) = 0 := by decide +kernel

-- Divisor correction at degree zero is retained even though its divisor factor vanishes.
example : planeLowPsiValueWith initialTable
    (key 0 [⟨.hyperplane, 1⟩, ⟨.hyperplane, 0⟩]) = 0 := by decide +kernel

-- The initial table has a proof, so its extension is an equality with the original algorithm.
example : planeLowPsiValue (key 0 [⟨.hyperplane, 1⟩]) = -1 / 960 := by
  rw [← planeLowPsiValueWith_eq 0 initialTable initial_checked _ rfl (by decide) (by decide)]
  decide +kernel

-- These formal triples test normalization arithmetic only, not quartic GW certification.
private def formalTable : ℕ → Fin 3 → ℚ := fun _ ↦ ![27, 42, 25 / 4]

example : planeLowPsiValueWith formalTable
    (key 4 (⟨.hyperplane, 1⟩ :: ⟨.hyperplane, 0⟩ :: List.replicate 12 ⟨.point, 0⟩)) =
      195 := by decide +kernel

-- Two repeated primary divisors produce two separate cup-product correction terms.
example : planeLowPsiValueWith formalTable
    (key 4 (⟨.hyperplane, 1⟩ :: ⟨.hyperplane, 0⟩ :: ⟨.hyperplane, 0⟩ ::
      List.replicate 12 ⟨.point, 0⟩)) = 888 := by decide +kernel

-- A primary unit triggers string reduction; a descendant unit triggers dilaton reduction.
example : planeLowPsiValueWith formalTable
    (key 4 (⟨.hyperplane, 1⟩ :: ⟨.unit, 0⟩ :: List.replicate 13 ⟨.point, 0⟩)) =
      108 := by decide +kernel

example : planeLowPsiValueWith formalTable
    (key 4 (⟨.unit, 1⟩ :: List.replicate 13 ⟨.point, 0⟩)) = 405 := by decide +kernel

-- Relabelling moves the descendant together with its state, including repeated points.
example : planeLowPsiValueWith formalTable
    (key 4 (⟨.hyperplane, 0⟩ :: List.replicate 12 ⟨.point, 0⟩ ++ [⟨.hyperplane, 1⟩])) =
      195 := by decide +kernel

-- Query conversion preserves the full degree and descendant sum on its ordered marking set.
example : (planeLowPsiQueryKey
    ⟨2, ![4], [⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩]⟩ rfl).beta = ![4] := rfl

example : (planeLowPsiQueryKey
    ⟨2, ![4], [⟨.hyperplane, 0⟩, ⟨.point, 0⟩, ⟨.hyperplane, 1⟩]⟩ rfl).totalPsi = 1 := by
  decide +kernel
