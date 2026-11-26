/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.CotangentCombination
public import AxiomaticGW.Tautological.RelationCertificate

/-!
# Replay of a computed cotangent combination in a held graph frame

The lookup is untrusted until each actual term is proved isomorphic to its
selected column. Exact coordinate equality then certifies the entire formal
sum, including negative coefficients and repeated terms. A missing graph
cannot silently become the default column: the coverage proof rejects it.
-/

@[expose] public section

namespace AxiomaticGW.CotangentCombination
open GluingExpression RelationCertificate

variable {g n : ℕ} {S : Type} [Fintype S] [NeZero n]

/-- Executable candidate lookup; the separate coverage check proves its meaning. -/
def columnIndex (frame : Fin n → DecoratedStableGraph S) (t : CotangentTerm g S) : Fin n :=
  ((List.finRange n).find? fun i ↦
    (t.expression.decoratedGraph t.decoration).isomorphic? (frame i)).getD 0

/-- Consolidate raw rational coefficients after the finite candidate lookup. -/
def coordinates (frame : Fin n → DecoratedStableGraph S) (r : CotangentCombination g S) :
    Coordinates n :=
  (r.map fun t ↦ Pi.single (columnIndex frame t.2) t.1).sum

/-- Coverage and exact arithmetic bind a table to the actual constructed graphs. -/
theorem strata_eq_interpret (frame : Fin n → DecoratedStableGraph S)
    (hf : ∀ i, (frame i).graph.totalGenus = g) (r : CotangentCombination g S)
    (hc : ∀ t ∈ r,
      (t.2.expression.decoratedGraph t.2.decoration).isomorphic?
        (frame (columnIndex frame t.2)) = true) :
    r.strata = interpret (fun i ↦ TautologicalStratum.mk (frame i) (hf i))
      (coordinates frame r) := by
  rw [coordinates, map_multiset_sum, Multiset.map_map]
  unfold strata
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro t ht
  simp only [Function.comp_apply, interpret, Fintype.linearCombination_apply_single]
  congr 2
  apply Quotient.sound
  exact (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp (hc t ht)

end AxiomaticGW.CotangentCombination
