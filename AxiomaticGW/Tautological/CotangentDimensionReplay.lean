/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.DecoratedComponentDimension
public import AxiomaticGW.Tautological.CotangentReplay

/-!
# Cotangent replay with justified component dimension pruning

Finite coordinate data may omit a term only when the executable component
dimension test proves its realized class is zero. Every retained graph must
still be isomorphic to its proposed destination, including all node powers.
The conclusion is an equality of realized classes, not of free strata.
-/

@[expose] public section

namespace AxiomaticGW.CotangentCombination
open GluingExpression RelationCertificate

variable {g n : ℕ} {S : Type} [Fintype S] [NeZero n]

/-- Coordinate records retain multiplicities; pruned terms contribute a zero record. -/
def dimensionRecords (lookup : DecoratedStableGraph S → Fin n)
    (k : S → ℕ) (r : CotangentCombination g S) : Multiset (Fin n × ℚ) :=
  r.map fun t ↦
    if t.2.expression.exceedsComponentDimension t.2.decoration k then (0, 0)
    else (lookup ((t.2.expression.decoratedGraph t.2.decoration).addLegPsi k), t.1)

/-- Exact addition of rational coefficients at their retained finite indices. -/
def recordCoordinates (data : Multiset (Fin n × ℚ)) : Coordinates n :=
  (data.map fun t ↦ Pi.single t.1 t.2).sum

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R} {I : StableCurveIntegration C}
attribute [local instance] strataRealizationModule

/-- Checked retained graphs and component vanishing justify the entire coordinate replay. -/
theorem map_mulLegPsi_eq_interpret_dimensionRecords
    (A : ∀ g S, [Fintype S] → StrataRealization C g S)
    (F : SeparatingPushforward C I) (N : NonseparatingPushforward C I) (P : PsiClasses C)
    (frame : Fin n → DecoratedStableGraph S) (hf : ∀ i, (frame i).graph.totalGenus = g)
    (lookup : DecoratedStableGraph S → Fin n) (k : S → ℕ) (r : CotangentCombination g S)
    (hc : ∀ t ∈ r, t.2.expression.Compatible A F N ∧
      t.2.expression.CotangentCompatible A P)
    (hp : ∀ t ∈ r, (A g S).LegPsiCompatible P t.2.expression.stable)
    (himage : ∀ t ∈ r, t.2.expression.exceedsComponentDimension t.2.decoration k = false →
      ((t.2.expression.decoratedGraph t.2.decoration).addLegPsi k).isomorphic?
        (frame (lookup ((t.2.expression.decoratedGraph t.2.decoration).addLegPsi k))) = true) :
    (A g S).map (StrataModule.mulLegPsi k r.strata) =
      (A g S).map (interpret (fun i ↦ TautologicalStratum.mk (frame i) (hf i))
        (recordCoordinates (dimensionRecords lookup k r))) := by
  simp only [strata, dimensionRecords, recordCoordinates, map_multiset_sum,
    Multiset.map_map, Function.comp_def, map_smul, StrataModule.mulLegPsi_basis]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro t ht
  by_cases hd : t.2.expression.exceedsComponentDimension t.2.decoration k = true
  · simp only [hd, ↓reduceIte, Pi.single_zero, map_zero]
    rw [t.2.expression.map_addLegPsi_eq_zero_of_component_dimension A F N P
      t.2.decoration k (hc t ht).1 (hc t ht).2 (hp t ht) hd, smul_zero]
  · have he : (t.2.expression.decoratedStratum t.2.decoration).addLegPsi k =
        TautologicalStratum.mk
          (frame (lookup ((t.2.expression.decoratedGraph t.2.decoration).addLegPsi k)))
          (hf _) := by
      apply Quotient.sound
      exact (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
        (himage t ht (Bool.eq_false_of_not_eq_true hd))
    simp only [Bool.eq_false_of_not_eq_true hd, Bool.false_eq_true, ↓reduceIte,
      interpret, Fintype.linearCombination_apply_single, map_smul, he]

end AxiomaticGW.CotangentCombination
