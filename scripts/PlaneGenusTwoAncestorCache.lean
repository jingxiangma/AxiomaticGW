/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests
public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine
public import AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate

/-!
# Candidate dependency table for the complete plane few-marking suite

The native explorer closes the independently held requests under the original
ancestor equations, then evaluates the rows in increasing total psi degree.
Every dependency must already have a value. These outputs are candidates;
the separate Lean replay checks the actual equations and incoming requests.
Run with `lake exe planeGenusTwoAncestorCache OUTPUT`.
-/

@[expose] public section
set_option maxRecDepth 20000

namespace AxiomaticGW.PlaneGenusTwoAncestorCacheExport
open Lean BelorousskiPandharipande SurfaceGenusTwo

abbrev Key := SurfaceAncestorKey .plane

/-- Full plane key: genus, curve coordinate, then paired basis codes and powers. -/
def keyCode (q : Key) : List ℕ :=
  [q.genus, q.beta 0] ++ q.orderedInsertions.flatMap (fun t ↦ [t.label.sortCode, t.psi])

def decodeInsertions : List ℕ → Except String (List (SurfaceInsertion .plane))
  | [] => .ok []
  | a :: k :: rest => do
    let label ← match a with
      | 0 => .ok SurfaceBasisLabel.unit
      | 1 => .ok SurfaceBasisLabel.hyperplane
      | 2 => .ok SurfaceBasisLabel.point
      | _ => .error "invalid plane basis code"
    return ⟨label, k⟩ :: (← decodeInsertions rest)
  | _ => .error "unpaired insertion code"

def decodeKey : List ℕ → Except String Key
  | 2 :: d :: rest => do
    let ins ← decodeInsertions rest
    return ⟨2, ![d], ins, by omega⟩
  | _ => .error "residual query is not a full genus-two key"

def keys (p : Multiset Key) : IO (List Key) := do
  let codes := (p.map keyCode).sort (· ≤ ·)
  codes.mapM fun code ↦ match decodeKey code with
    | .ok q => pure q
    | .error message => throw (IO.userError message)

/-- The unchanged stable-map descendant comparison, retaining all ordered insertions. -/
def queryTerms (q : SurfaceQuery .plane) : RationalTerms Key :=
  SurfaceDescendant.mixedAncestorTerms 2 (Fin q.insertions.length)
    (by simp only [StableArity, Fintype.card_fin]; omega)
    (List.finRange q.insertions.length) q.beta (fun i ↦ (q.insertions.get i).psi) 0
    (fun i ↦ (q.insertions.get i).label)

def ratJSON (q : ℚ) : Json := toJson [q.num, (q.den : ℤ)]

def queryJSON (q : SurfaceQuery .plane) : Json :=
  Json.mkObj [("genus", toJson q.genus), ("curve", toJson [q.beta 0]),
    ("insertions", toJson (q.insertions.map fun t ↦ [t.label.sortCode, t.psi]))]

def termsJSON (p : RationalTerms Key) : String :=
  let terms := (p.map fun t ↦
    (Json.mkObj [("coefficient", ratJSON t.1),
      ("monomial", toJson ((t.2.map keyCode).sort (· ≤ ·)))]).compress).sort (· ≤ ·)
  "[" ++ String.intercalate "," terms ++ "]"

def lookup (entries : Array (Key × ℚ)) (q : Key) : ℚ :=
  ((entries.find? fun entry ↦ entry.1 == q).map Prod.snd).getD 0

/-- Full dependency closure and bottom-up candidate values; missing dependencies fail. -/
def explore : IO String := do
  let mut pending : Array Key := #[]
  let mut requests : Array (SurfaceQuery .plane × RationalTerms Key) := #[]
  let stderr ← IO.getStderr
  for i in List.finRange 48 do
    let q := GenusTwoPlaneFewMarkingRequests.requests i
    let p := queryTerms q
    requests := requests.push (q, p)
    for r in ← keys (p.bind Prod.snd) do
      if !pending.contains r then pending := pending.push r
  let rootCount := pending.size
  let mut rows : Array (Key × RationalTerms Key) := #[]
  let mut cursor := 0
  while cursor < pending.size do
    let some q := pending[cursor]? | throw (IO.userError "invalid worklist cursor")
    let p := if hk : 1 < q.totalPsi then ancestorReductionTerms q hk else 0
    for r in ← keys (p.bind Prod.snd) do
      unless r.totalPsi < q.totalPsi do
        throw (IO.userError "ancestor dependency does not strictly lower total psi degree")
      if !pending.contains r then pending := pending.push r
    rows := rows.push (q, p)
    cursor := cursor + 1
    stderr.putStrLn s!"ancestor row {cursor}/{pending.size}: psi={q.totalPsi}, terms={p.card}"
  let ordered := rows.toList.mergeSort (fun p q ↦ p.1.totalPsi ≤ q.1.totalPsi)
  let mut entries : Array (Key × ℚ) := #[]
  let mut records : Array String := #[]
  for (q, p) in ordered do
    for r in ← keys (p.bind Prod.snd) do
      unless entries.any (fun entry ↦ entry.1 == r) do
        throw (IO.userError "missing ancestor dependency in bottom-up evaluation")
    let v := if q.totalPsi ≤ 1 then
      planeLowPsiValueWith GenusTwoPlaneLine.values q else RationalTerms.eval (lookup entries) p
    entries := entries.push (q, v)
    records := records.push ("{\"key\":" ++ (toJson (keyCode q)).compress ++
      ",\"value\":" ++ (ratJSON v).compress ++ ",\"terms\":" ++ termsJSON p ++ "}")
  let mut incoming : Array String := #[]
  for (q, p) in requests do
    for r in ← keys (p.bind Prod.snd) do
      unless entries.any (fun entry ↦ entry.1 == r) do
        throw (IO.userError "missing dependency of an incoming descendant request")
    incoming := incoming.push ("{\"query\":" ++ (queryJSON q).compress ++
      ",\"value\":" ++ (ratJSON (RationalTerms.eval (lookup entries) p)).compress ++
      ",\"terms\":" ++ termsJSON p ++ "}")
  stderr.putStrLn s!"complete: {rootCount} distinct roots, {entries.size} closed ancestor rows"
  return "{\"schema_version\":1,\"kind\":\"axiomatic_gw.plane_genus_two_ancestor_cache\"," ++
    "\"proof_status\":\"candidate_data\",\"ancestor_rows\":[" ++
    String.intercalate "," records.toList ++ "],\"requests\":[" ++
    String.intercalate "," incoming.toList ++ "]}\n"

end AxiomaticGW.PlaneGenusTwoAncestorCacheExport

def main (args : List String) : IO Unit := do
  let output ← AxiomaticGW.PlaneGenusTwoAncestorCacheExport.explore
  match args with
  | [path] => IO.FS.writeFile path output
  | [] => IO.print output
  | _ => throw (IO.userError "expected at most one output path")
