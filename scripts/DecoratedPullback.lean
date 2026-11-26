/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Tautological.BelorousskiPandharipandeForgetful

/-!
# Export the actual Lean decorated-pullback computation for external comparison

`lake exe decoratedPullback` writes JSON to stdout.
The native output is diagnostic evidence; the general pullback identity and
graph bounds are independently proved in Lean. Sorting serialized terms only
chooses an output order and preserves all signed repetitions.
-/

@[expose] public section

open AxiomaticGW GluingExpression BelorousskiPandharipande Lean

namespace AxiomaticGW.DecoratedPullback

/-- Incidence and every cotangent flag of an actual finite graph. -/
def graphJSON {n : ℕ} (G : DecoratedStableGraph (Fin n)) : Json :=
  Json.mkObj [
    ("genus", toJson ((List.finRange G.graph.vertexCount).map G.graph.genus)),
    ("leg_vertices", toJson ((List.finRange n).map fun i ↦ (G.graph.legVertex i).val)),
    ("endpoints", toJson ((List.finRange G.graph.edgeCount).map fun e ↦
      [(G.graph.endpoint e 0).val, (G.graph.endpoint e 1).val])),
    ("leg_psi", toJson ((List.finRange n).map G.legPsiPower)),
    ("half_psi", toJson ((List.finRange G.graph.edgeCount).map fun e ↦
      [G.halfEdgePsiPower e 0, G.halfEdgePsiPower e 1])),
    ("codimension", toJson G.codimension)]

/-- One named original term and its complete signed pullback. -/
def caseJSON {g m : ℕ} (name : String) (z : CotangentTerm g (Fin m)) (n : ℕ) : String :=
  let terms := ((z.addMarkings n).map fun t ↦
    (Json.mkObj [("coefficient", toJson t.1), ("graph", graphJSON
      ((t.2.expression.decoratedGraph t.2.decoration).relabel
        (ExtraMarkings.finEquiv n m)))]).compress).sort (· ≤ ·)
  let header := (Json.mkObj [("name", toJson name), ("genus", toJson g),
    ("initial_markings", toJson m), ("additional_markings", toJson n),
    ("original", graphJSON (z.expression.decoratedGraph z.decoration))]).compress
  header.dropEnd 1 |>.toString ++ ",\"terms\":[" ++ String.intercalate "," terms ++ "]}"

/-- A loop with unequal decorations on its two original branches. -/
def loopCase : CotangentTerm 2 (Fin 1) :=
  (CotangentTerm.fundamental 1 (Option (Option (Fin 1))) (by norm_num [StableArity])
    (fun | none => 1 | some none => 2 | some (some _) => 0)).nonseparating

/-- Both placements at equal unmarked elliptic components must survive. -/
def symmetricCase : CotangentTerm 2 (Fin 0) :=
  ((CotangentTerm.fundamental 1 (Option (Fin 0)) (by norm_num [StableArity]) (fun _ ↦ 0)).separating
    (CotangentTerm.fundamental 1 (Option (Fin 0)) (by norm_num [StableArity]) (fun _ ↦ 0))).relabel
    finSumFinEquiv

end AxiomaticGW.DecoratedPullback

open AxiomaticGW.DecoratedPullback

/-- Export all twenty BP diagrams, all six assignments, plus power and symmetry regressions. -/
def main : IO Unit := do
  let mut cases := []
  for n in [1, 2] do
    for i in List.finRange 20 do
      for e in List.finRange 6 do
        cases := cases ++ [caseJSON s!"bp_{i.val}_{e.val}" (orbitCotangentTerm i e) n]
    cases := cases ++ [
      caseJSON "psi_square" (CotangentTerm.fundamental 2 (Fin 1)
        (by norm_num [StableArity]) (fun _ ↦ 2)) n,
      caseJSON "psi_product" (CotangentTerm.fundamental 2 (Fin 2)
        (by norm_num [StableArity]) ![2, 1]) n,
      caseJSON "zero_power" (CotangentTerm.fundamental 2 (Fin 1)
        (by norm_num [StableArity]) (fun _ ↦ 0)) n,
      caseJSON "unmarked_zero" (CotangentTerm.fundamental 2 (Fin 0)
        (by norm_num [StableArity]) Fin.elim0) n,
      caseJSON "loop_branches" loopCase n,
      caseJSON "symmetric" symmetricCase n]
  IO.println ("{\"schema_version\":1,\"cases\":[" ++ String.intercalate "," cases ++ "]}")
