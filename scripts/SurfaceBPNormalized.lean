/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.GenusTwoNormalizedBP

/-! Exact exploration export for the checked first-descendant BP normalization. -/

@[expose] public section
namespace AxiomaticGW.SurfaceBPNormalizedExport
open Lean SurfacePolynomialReduction

/-- The same display codes as the original BP exploration export. -/
def labelCode {X : SurfaceTarget} : SurfaceBasisLabel X → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .point => 2
  | .exceptional i => 3 + i.val

def insertionJSON {X : SurfaceTarget} (m : Multiset (SurfaceInsertion X)) : Json :=
  toJson ((m.map fun i ↦ [labelCode i.label, i.psi]).sort (· ≤ ·))

def ancestorJSON {X : SurfaceTarget} (q : SurfaceAncestorKey X) : Json :=
  Json.mkObj [("genus", toJson q.genus),
    ("curve", toJson ((List.finRange (X.blowups + 1)).map q.beta)),
    ("insertions", insertionJSON q.insertions)]

def variableJSON {X : SurfaceTarget} : Variable X → Json
  | .inl q => Json.mkObj [("kind", toJson "ancestor"), ("query", ancestorJSON q)]
  | .inr q => Json.mkObj [("kind", toJson "descendant"), ("query", Json.mkObj
      [("genus", toJson q.genus),
       ("curve", toJson ((List.finRange (X.blowups + 1)).map q.beta)),
       ("insertions", insertionJSON (q.insertions : Multiset (SurfaceInsertion X)))])]

def termsJSON {σ : Type} (toQuery : σ → Json) (p : RationalTerms σ) : String :=
  let terms := (p.map fun t ↦
    "{\"coefficient\":" ++ (toJson [t.1.num, (t.1.den : ℤ)]).compress ++
      ",\"monomial\":[" ++ String.intercalate ","
        ((t.2.map (fun q ↦ (toQuery q).compress)).sort (· ≤ ·)) ++ "]}").sort (· ≤ ·)
  "[" ++ String.intercalate "," terms ++ "]"

def caseJSON (name : String) (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel X) : String :=
  let original := BelorousskiPandharipande.genusTwoTerms X n beta 0
    (SurfaceGenusZero.pointLabels a n)
  let normalized := RationalTerms.affineSubstitute normalizedTerms original
  let substitutions := (original.bind Prod.snd).dedup.map fun q ↦
    "{\"ancestor\":" ++ (ancestorJSON q).compress ++ ",\"terms\":" ++
      termsJSON variableJSON (normalizedTerms q) ++ "}"
  let header := (Json.mkObj [("name", toJson name), ("blowups", toJson X.blowups),
    ("curve", toJson ((List.finRange (X.blowups + 1)).map beta)),
    ("additional_markings", toJson n),
    ("labels", toJson ((List.finRange 3).map (fun i ↦ labelCode (a i))))]).compress
  header.dropEnd 1 |>.toString ++ ",\"ancestor_terms\":" ++ termsJSON ancestorJSON original ++
    ",\"normalized_terms\":" ++ termsJSON variableJSON normalized ++ ",\"substitutions\":[" ++
    String.intercalate "," (substitutions.sort (· ≤ ·)) ++ "]}"

def probeJSON {X : SurfaceTarget} (name : String) (q : SurfaceAncestorKey X) : String :=
  let header := (Json.mkObj [("name", toJson name), ("blowups", toJson X.blowups),
    ("ancestor", ancestorJSON q)]).compress
  header.dropEnd 1 |>.toString ++ ",\"terms\":" ++ termsJSON variableJSON (normalizedTerms q) ++ "}"

end AxiomaticGW.SurfaceBPNormalizedExport
open AxiomaticGW SurfaceBPNormalizedExport

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
      stderr.putStrLn s!"Normalizing {name}"
      cases := cases ++ [run ()]
  let probes := [
    probeJSON "f1_2E_psiE_ptpt" (⟨2, ![2,0],
      {⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩}, by decide +kernel⟩ :
        SurfaceAncestorKey .hirzebruchOne),
    probeJSON "f1_2E_psiE_Eptpt" (⟨2, ![2,0],
      {⟨.exceptional 0, 1⟩, ⟨.exceptional 0, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩},
      by decide +kernel⟩ : SurfaceAncestorKey .hirzebruchOne),
    probeJSON "f1_EF_psiE_ptptpt" (⟨2, ![1,1],
      {⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩, ⟨.point, 0⟩}, by decide +kernel⟩ :
        SurfaceAncestorKey .hirzebruchOne),
    probeJSON "bl2_2E1_psiE1_ptpt" (⟨2, ![2,0,0],
      {⟨.exceptional 0, 1⟩, ⟨.point, 0⟩, ⟨.point, 0⟩}, by decide +kernel⟩ :
        SurfaceAncestorKey .blowupTwo),
    probeJSON "p2_line_psi3pt_retained" (⟨2, ![1], {⟨.point, 3⟩}, by decide +kernel⟩ :
      SurfaceAncestorKey .plane)]
  IO.println ("{\"schema_version\":1,\"cases\":[" ++ String.intercalate "," cases ++
    "],\"probes\":[" ++ String.intercalate "," probes ++ "]}")
