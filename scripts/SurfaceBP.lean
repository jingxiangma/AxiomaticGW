/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.BelorousskiPandharipande

/-!
# Diagnostic export of exact surface BP equations

The native export is compared with independent incidence-based contractions
in Sage. General soundness and support bounds are kernel proofs in the
imported modules. Lower-genus values in the export come from the existing
algorithms; the external comparison does not independently certify them.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceBPExport
open Lean

/-- Version-one state codes: unit, hyperplane, point, then exceptional divisors. -/
def labelCode {X : SurfaceTarget} : SurfaceBasisLabel X → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .point => 2
  | .exceptional i => 3 + i.val

/-- A full ancestor request with stable, permutation-independent insertion order. -/
def queryJSON {X : SurfaceTarget} (q : SurfaceAncestorKey X) : Json :=
  Json.mkObj [("genus", toJson q.genus),
    ("curve", toJson ((List.finRange (X.blowups + 1)).map q.beta)),
    ("insertions", toJson ((q.insertions.map fun i ↦
      [labelCode i.label, i.psi]).sort (· ≤ ·)))]

/-- Preserve exact rational numerators and denominators. -/
def ratJSON (q : ℚ) : Json := toJson [q.num, (q.den : ℤ)]

/-- Uncollected monomials retain every coefficient and repeated variable. -/
def termsJSON {X : SurfaceTarget} (p : RationalTerms (SurfaceAncestorKey X)) : String :=
  let terms := (p.map fun t ↦
    "{\"coefficient\":" ++ (ratJSON t.1).compress ++ ",\"monomial\":[" ++
      String.intercalate "," ((t.2.map (fun q ↦ (queryJSON q).compress)).sort (· ≤ ·)) ++ "]}"
    ).sort (· ≤ ·)
  "[" ++ String.intercalate "," terms ++ "]"

/-- Dimension filtering only: all genus-zero/one variables remain visible here. -/
def symbolicVertex (X : SurfaceTarget) :
    SurfaceVertexValues X (RationalTerms (SurfaceAncestorKey X)) :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q.DimensionCompatible then RationalTerms.term 1 {q} else 0

/-- Export both stages so the external checker can distinguish graph contraction
from the substitution of independently formalized lower-genus algorithms. -/
def caseJSON (name : String) (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) : String :=
  let labels := SurfaceGenusZero.pointLabels a n
  let raw := BelorousskiPandharipande.surfaceTerms X (symbolicVertex X) n beta 0 labels
  let reduced := BelorousskiPandharipande.genusTwoTerms X n beta 0 labels
  let low := ((raw.bind Prod.snd).dedup.filter (fun q ↦ q.genus ≤ 1)).map fun q ↦
    (Json.mkObj [("query", queryJSON q), ("value", ratJSON
      (SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q))]).compress
  let header := (Json.mkObj [("name", toJson name), ("blowups", toJson X.blowups),
    ("curve", toJson ((List.finRange (X.blowups + 1)).map beta)),
    ("additional_markings", toJson n),
    ("labels", toJson ((List.finRange 3).map (fun i ↦ labelCode (a i))))]).compress
  header.dropEnd 1 |>.toString ++ ",\"symbolic_terms\":" ++ termsJSON raw ++
    ",\"genus_two_terms\":" ++ termsJSON reduced ++ ",\"lower_values\":[" ++
    String.intercalate "," (low.sort (· ≤ ·)) ++ "]}"

end AxiomaticGW.SurfaceBPExport

open AxiomaticGW SurfaceBPExport

/-- Small exact equations test all three targets and distinguish equal-energy classes. -/
def main (args : List String) : IO Unit := do
  let jobs : List (String × (Unit → String)) := [
    ("p2_zero_HH1", fun _ ↦
      caseJSON "p2_zero_HH1" .plane ![0] 0 ![.hyperplane, .hyperplane, .unit]),
    ("p2_line_HHH", fun _ ↦ caseJSON "p2_line_HHH" .plane ![1] 2 (fun _ ↦ .hyperplane)),
    ("f1_E_EEE", fun _ ↦ caseJSON "f1_E_EEE" .hirzebruchOne ![1,0] 0 (fun _ ↦ .exceptional 0)),
    ("f1_F_HHH", fun _ ↦ caseJSON "f1_F_HHH" .hirzebruchOne ![0,1] 1 (fun _ ↦ .hyperplane)),
    ("f1_F_EHH", fun _ ↦
      caseJSON "f1_F_EHH" .hirzebruchOne ![0,1] 1 ![.exceptional 0, .hyperplane, .hyperplane]),
    ("bl2_E1_E1E1E1", fun _ ↦
      caseJSON "bl2_E1_E1E1E1" .blowupTwo ![1,0,0] 0 (fun _ ↦ .exceptional 0)),
    ("bl2_E2_E1E1E1", fun _ ↦
      caseJSON "bl2_E2_E1E1E1" .blowupTwo ![0,1,0] 0 (fun _ ↦ .exceptional 0)),
    ("bl2_E2_E2E2E2", fun _ ↦
      caseJSON "bl2_E2_E2E2E2" .blowupTwo ![0,1,0] 0 (fun _ ↦ .exceptional 1)),
    ("bl2_L_HHH", fun _ ↦ caseJSON "bl2_L_HHH" .blowupTwo ![0,0,1] 0 (fun _ ↦ .hyperplane)),
    ("bl2_L_E1E2H", fun _ ↦
      caseJSON "bl2_L_E1E2H" .blowupTwo ![0,0,1] 0 ![.exceptional 0, .exceptional 1, .hyperplane])]
  let stderr ← IO.getStderr
  let mut cases := []
  for (name, run) in jobs do
    if args.isEmpty || args.contains name then
      stderr.putStrLn s!"Expanding {name}"
      cases := cases ++ [run ()]
  IO.println ("{\"schema_version\":1,\"cases\":[" ++ String.intercalate "," cases ++ "]}")
