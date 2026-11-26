import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointPair
import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsDescendants
import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsPsiSix
import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointAncestor

open AxiomaticGW BelorousskiPandharipande SurfaceGenusTwo
open GKM.PlaneGenusTwoAncestors

set_option maxRecDepth 20000

private def lowQueries : Finset (SurfaceAncestorKey .plane) :=
  {key 0, key 1, key 2, key 3, key 4, key 5}

-- Actual low-psi ancestor normalization uses only the previously accepted canonical table.
private theorem lowAccepted :
    checkAncestorValues (planeLowPsiValueWith GenusTwoPlaneLine.values)
      lowQueries values = true := by decide +kernel

example : value 2 = planeAncestorValueWith GenusTwoPlaneLine.values (key 2) := by
  rw [← values_key]
  exact checkAncestorValues_sound _ lowQueries values lowAccepted (key 2) (by decide +kernel)

-- The supported full descendant query is evaluated through this accepted partial cache.
example : planeQueryValueCached? GenusTwoPlaneLine.values lowQueries values
    ⟨2, ![0], [⟨.hyperplane, 1⟩]⟩ = some (-1 / 960) := by decide +kernel

-- The whole original query interface is preserved even when a query misses the cache.
example (q : SurfaceQuery .plane) (hb : q.beta 0 ≤ 1) :
    planeQueryValueCached? GenusTwoPlaneLine.values lowQueries values q = planeQueryValue? q :=
  planeQueryValueCached?_eq 1 _ GenusTwoPlaneLine.accepted _ _ lowAccepted q hb

-- An empty table is a valid cache and falls back to the original evaluator everywhere.
example (base values : SurfaceAncestorKey .plane → ℚ) :
    ancestorValueCached base ∅ values = ancestorValue base := by
  apply ancestorValueCached_eq
  simp only [checkAncestorValues, Finset.forall_mem_empty_iff, decide_true]

-- A coherent scalar encoding cannot change a terminal value.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values) lowQueries
    (fun q ↦ if q = key 2 then 0 else values q) (key 2) = false := by decide +kernel

-- Changing only the full class invalidates the claimed nonzero degree-zero terminal.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values) lowQueries
    (fun _ ↦ -1 / 960)
    ⟨2, ![1], ([⟨.hyperplane, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩ = false := by
  decide +kernel

-- Neither a changed state nor a changed power can reuse that terminal value.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values) lowQueries
    (fun _ ↦ -1 / 960)
    ⟨2, ![0], ([⟨.point, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩ = false := by
  decide +kernel

example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values) lowQueries
    (fun _ ↦ -1 / 960)
    ⟨2, ![0], ([⟨.hyperplane, 0⟩] : List (SurfaceInsertion .plane)), by decide⟩ = false := by
  decide +kernel

-- Genus is checked even when an unrelated row has a matching rational value.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values) lowQueries
    (fun _ ↦ 0)
    ⟨1, ![0], ([⟨.hyperplane, 1⟩] : List (SurfaceInsertion .plane)), by decide⟩ = false := by
  decide +kernel

example : planeQueryValueCached? GenusTwoPlaneLine.values lowQueries values
    ⟨1, ![0], [⟨.hyperplane, 1⟩]⟩ = none := by decide +kernel

-- Even the correct row value cannot pass when its actual residual query is omitted.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
    {key 7} values (key 7) = false := by
  simp only [checkAncestorRow, show (key 7).genus = 2 by decide +kernel,
    true_and, dif_neg (show ¬(key 7).totalPsi ≤ 1 by decide +kernel),
    ancestorStep, PsiTwo.reduction_7]
  decide +kernel

-- The new component certificate checks the original point-ancestor row.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
    queries values (key 12) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 12).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [GKM.PlaneGenusTwoPointAncestor.reduction]
  decide +kernel

example : planeAncestorValueWith GenusTwoPlaneLine.values (key 12) = -9 / 640 :=
  GKM.PlaneGenusTwoPointAncestor.value

-- A changed boundary coefficient is rejected against the original complete equation.
example : ancestorReductionTerms (key 7) (by decide +kernel) ≠
    RationalTerms.scale 2 (terms 7) := by
  rw [PsiTwo.reduction_7]
  decide +kernel

-- Exercise the public derivation against the original full descendant query.
example : planeQueryValue? ⟨2, ![1], [⟨.point, 1⟩, ⟨.point, 1⟩]⟩ = some (1 / 144) :=
  GKM.PlaneGenusTwoPointPair.accepted

-- The named certificate binds to the precise incoming GKM claim.
example : planeQueryValue? (GKM.PlaneGenusTwoFewMarkingsReplay.requests 46) =
    some (GKM.PlaneGenusTwoFewMarkingsReplay.values 46) :=
  GKM.PlaneGenusTwoPointPair.gkm_accepted

-- The original product equation retains its lower-genus constant and genus-two variable.
example : planeAncestorValueWith GenusTwoPlaneLine.values (key 11) =
    29 / 2880 + 3 * planeAncestorValueWith GenusTwoPlaneLine.values (key 2) :=
  GKM.PlaneGenusTwoPointPair.ancestor_equation

-- All incoming expansions and their cache arithmetic are checked. Full ancestor
-- table acceptance remains a separate hypothesis of the final reconstruction theorem.
example (i : Fin 48) :
    planeQueryValueCached? GenusTwoPlaneLine.values queries values
      (GKM.PlaneGenusTwoFewMarkingsReplay.requests i) =
      some (GKM.PlaneGenusTwoFewMarkingsReplay.values i) := cached_computation i

example : mixedTerms (GKM.PlaneGenusTwoFewMarkingsReplay.requests 46) =
    comparisonTerms_46 := comparison_46

-- A highest-power zero is justified by the complete original boundary equation.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
    queries values (key 35) = true := by
  rw [checkAncestorRow, decide_eq_true_eq]
  refine ⟨by decide +kernel, ?_⟩
  rw [dif_neg (show ¬(key 35).totalPsi ≤ 1 by decide +kernel)]
  unfold ancestorStep
  rw [PsiSix.reduction_35]
  decide +kernel

-- The proved zero cannot authorize a different value in that row.
example : checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)
    queries (fun q ↦ if q = key 35 then 1 else values q) (key 35) = false := by
  simp only [checkAncestorRow, show (key 35).genus = 2 by decide +kernel,
    true_and, dif_neg (show ¬(key 35).totalPsi ≤ 1 by decide +kernel),
    ancestorStep, PsiSix.reduction_35]
  decide +kernel
