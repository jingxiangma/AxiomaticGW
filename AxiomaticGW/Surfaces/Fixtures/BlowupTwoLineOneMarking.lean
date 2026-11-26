/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineOneMarkingAncestors
public import AxiomaticGW.Surfaces.Fixtures.BlowupTwoLineBPRows
public import AxiomaticGW.Surfaces.GenusTwoOneMarkingTransfer

/-!
# Genus-two one-marked stable-map descendants on the strict line

For L = H − E₁ − E₂, the divisor correction uses H with the opposite sign
from both exceptionals. The only other tail is the point at degree zero.
The point query reads the canonical P entry at L.
-/

@[expose] public section
namespace AxiomaticGW.BlowupTwoLineOneMarking
open BlowupTwoLineBP SurfaceGenusTwo SurfaceDescendant SurfaceGenusTwoBlowupOrder
open SurfaceGenusTwoBlowupDescendants

private abbrev X := SurfaceTarget.blowupTwo
private abbrev actual := SurfaceGenusTwoBlowupRecursion.values (X := X) 0

/-- The unit and three divisor queries at virtual dimension. -/
def highRequest (j : Fin 4) : SurfaceQuery .blowupTwo :=
  ⟨2, line, [⟨labels j, 3 - (labels j).codimension⟩]⟩

/-- The remaining one-marked basis query at the same virtual dimension. -/
def pointRequest : SurfaceQuery .blowupTwo := ⟨2, line, [⟨.point, 1⟩]⟩

/-- All four higher-power requests are stable and satisfy the surface dimension equation. -/
theorem high_domain (j : Fin 4) :
    (highRequest j).GeometricDomain ∧ (highRequest j).DimensionCompatible := by
  fin_cases j <;> decide +kernel

/-- The remaining basis request has the same stability and virtual-dimension properties. -/
theorem point_domain : pointRequest.GeometricDomain ∧ pointRequest.DimensionCompatible := by
  decide +kernel

private def lowKey : Fin 4 → SurfaceAncestorKey X :=
  ![oneMarkingKey 0 .hyperplane 1, oneMarkingKey 0 (.exceptional 0) 1,
    oneMarkingKey 0 (.exceptional 1) 1, oneMarkingKey 0 .point 0]

private def lowFamily : Fin 4 → Family X :=
  ![.hyperplane, .exceptional 0, .exceptional 1, .primary]

private def tails (j : Fin 4) : RationalTerms (SurfaceAncestorKey X) :=
  let term (c : ℚ) (r : Fin 4) := RationalTerms.term c {lowKey r}
  if j = 0 then term (-1) 0 + term 1 1 + term 1 2 + term (-2) 3
  else term 1 0 + term (-1) 1 + term (-1) 2 + term 1 3

private theorem transfer_terms (j : Fin 4) :
    oneMarkingTerms (reconstructedCalibrationMatrix X) line (labels j)
      (3 - (labels j).codimension) 0 =
      RationalTerms.term 1 {oneMarkingKey line (labels j) (3 - (labels j).codimension)} +
        tails j := by
  fin_cases j <;> decide +kernel

private theorem low_values (r : Fin 4) :
    ancestorValueWith actual (lowKey r) =
      (![-1/960, -1/2880, -1/2880, 0] : Fin 4 → ℚ) r := by
  have hg : (lowKey r).genus = 2 := by fin_cases r <;> rfl
  have hp : (lowKey r).totalPsi ≤ 1 := by fin_cases r <;> decide +kernel
  have ht : SurfacePolynomialReduction.normalizedTerms (lowKey r) =
      RationalTerms.term 1 {Sum.inr ((lowFamily r).query 0)} := by
    fin_cases r <;> decide +kernel
  rw [ancestorValueWith_of_canonical_singleton actual _ 0 (lowFamily r) hg hp ht]
  unfold actual
  rw [SurfaceGenusTwoBlowupRecursion.values_boundary 0 (0, lowFamily r) (map_zero _)]
  fin_cases r <;> decide +kernel

private theorem tail_value (j : Fin 4) :
    RationalTerms.eval (ancestorValueWith actual) (tails j) =
      if j = 0 then 1/2880 else -1/2880 := by
  unfold tails
  split_ifs <;> simp only [RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, Algebra.algebraMap_self_apply, low_values] <;> decide +kernel

private theorem original_query (q : SurfaceQuery X) :
    queryValue? 0 q = queryValueWith? actual q :=
  (queryValueWith?_eq_of_table 0 _ actual (fun _ _ ↦ rfl) q (le_refl _)).symm

/-- The complete mixed transfer gives 13/2880 for τ₃(1) and 1/240 for each τ₂(divisor). -/
theorem high_descendants (j : Fin 4) : queryValue? 0 (highRequest j) =
    some (if j = 0 then 13/2880 else 1/240) := by
  have h := high_ancestors (SurfaceGenusTwoBlowupLowPsi.ancestorValueWith actual) j
  change ancestorValueWith actual _ = _ at h
  rw [original_query, highRequest, queryValueWith?_oneMarking, transfer_terms,
    RationalTerms.eval_add, RationalTerms.eval_term, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, one_mul, h, tail_value]
  split_ifs <;> decide +kernel

/-- The mixed point query at L equals the hyperplane state by the complete canonical BP row. -/
theorem point_descendant : queryValue? 0 pointRequest =
    some (SurfaceGenusTwoBlowupRecursion.values 0 (line, .hyperplane)) := by
  have hm : oneMarkingTerms (reconstructedCalibrationMatrix X) line .point 1 0 =
      RationalTerms.term 1 {oneMarkingKey line .point 1} := by decide +kernel
  have ht : SurfacePolynomialReduction.normalizedTerms (oneMarkingKey line .point 1) =
      RationalTerms.term 1 {Sum.inr (Family.point.query line)} := by decide +kernel
  rw [original_query, pointRequest, queryValueWith?_oneMarking, hm, RationalTerms.eval_term,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, one_mul,
    ancestorValueWith_of_canonical_singleton actual _ line .point rfl (by decide +kernel) ht]
  exact congrArg some point_eq_hyperplane

end AxiomaticGW.BlowupTwoLineOneMarking
