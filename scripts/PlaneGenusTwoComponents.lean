/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsData
public import AxiomaticGW.Surfaces.GenusTwoCachedAncestors
public import AxiomaticGW.Surfaces.LowGenusAncestorDimension

/-!
# Candidate components for the complete plane genus-two ancestor table

Expand the original selected boundary before substituting lower-genus values.
Collect full component keys and export each proposed value once. Dimension
filtering and the native cotangent shortcut preserve the existing algorithms;
none of the proposed values is accepted without separate kernel replay.
Run with `lake exe planeGenusTwoComponents OUTPUT`.
-/

@[expose] public section

open Lean AxiomaticGW BelorousskiPandharipande SurfaceGenusTwo
open AxiomaticGW.GKM.PlaneGenusTwoAncestors
set_option maxRecDepth 65536

namespace AxiomaticGW.PlaneGenusTwoComponentsExport

abbrev Key := SurfaceAncestorKey .plane

def boundaryWith {S : Type} [Fintype S]
    (v : SurfaceVertexValues .plane (RationalTerms Key))
    (b : CotangentCombination 2 S) (beta : SurfaceTarget.plane.Curve) (k : S → ℕ)
    (a : S → SurfaceBasisLabel .plane) : RationalTerms Key :=
  b.bind fun t ↦ RationalTerms.scale (-t.1)
    (t.2.expression.surfaceDecoratedTerms .plane v t.2.decoration beta k a)

def ancestorWith (v : SurfaceVertexValues .plane (RationalTerms Key))
    (q : Key) (hk : 1 < q.totalPsi) : RationalTerms Key :=
  if hs : (squareMarks q).Nonempty then
    boundaryWith v (GenusTwoPsiSquare.boundaryRemainder
      (q.orderedInsertions.length - 1)) q.beta (squareLowerPowers q hs)
        (q.orderedLabels ∘ squareFrame q hs)
  else
    boundaryWith v (GenusTwoPsiProduct.boundaryRemainder
      (q.orderedInsertions.length - 2)) q.beta (productLowerPowers q hk hs)
        (q.orderedLabels ∘ productFrame q hk hs)

theorem ancestorWith_original (q : Key) (hk : 1 < q.totalPsi) :
    ancestorWith (vertexTerms .plane) q hk = ancestorReductionTerms q hk := rfl

def symbolic : SurfaceVertexValues .plane (RationalTerms Key) :=
  fun g S _ h beta k a ↦
    let q := SurfaceAncestorKey.ofLabels g S h beta k a
    if q.DimensionCompatible then RationalTerms.term 1 {q} else 0

def code (q : Key) : List ℕ :=
  [q.genus, q.beta 0] ++ q.orderedInsertions.flatMap (fun t ↦ [t.label.sortCode,t.psi])

def termsJSON (p : RationalTerms Key) : String :=
  let terms := (p.map fun t ↦
    (Json.mkObj [("coefficient", toJson [t.1.num,(t.1.den : ℤ)]),
      ("monomial", toJson ((t.2.map code).sort (· ≤ ·)))]).compress).sort (· ≤ ·)
  "[" ++ String.intercalate "," terms ++ "]"

/-- Native exploration uses the proved cotangent zero branches before recursion. -/
def componentValue (q : Key) : ℚ :=
  if q.genus = 0 ∧ q.insertions.card ≤ q.totalPsi + 2 then 0
  else if q.genus = 1 ∧ q.insertions.card < q.totalPsi then 0
  else SurfaceGenusOne.componentValue .plane (SurfaceGenusOne.ancestorValue .plane) q

/-- The exploration shortcut is exactly the existing lower-genus algorithm. -/
theorem componentValue_eq (q : Key) :
    componentValue q =
      SurfaceGenusOne.componentValue .plane (SurfaceGenusOne.ancestorValue .plane) q := by
  unfold componentValue
  split_ifs with hzero hone
  · rw [SurfaceGenusOne.componentValue, if_pos hzero.1]
    exact (SurfaceGenusZero.ancestorValue_zero_of_cotangent_bound q hzero.1 hzero.2).symm
  · rw [SurfaceGenusOne.componentValue, if_neg (by omega : q.genus ≠ 0)]
    exact (SurfaceGenusOne.ancestorValue_zero_of_cotangent_bound q hone.1 hone.2).symm
  · rfl

def componentQueries : IO (Finset Key × Array String) := do
  let mut qs : Finset Key := ∅
  let mut rows : Array String := #[]
  let stderr ← IO.getStderr
  let indices := List.finRange 39
  for i in indices do
    let q := key i
    if hk : 1 < q.totalPsi then
      let raw := ancestorWith symbolic q hk
      let low := (raw.map fun t ↦ t.2.toFinset.filter (fun q ↦ q.genus ≤ 1)).sup
      qs := qs ∪ low
      rows := rows.push ("{\"index\":" ++ toString i ++ ",\"symbolic_terms\":" ++
        termsJSON raw ++ "}")
      stderr.putStrLn s!"row {i}: {raw.card} terms, {low.card} component keys; {qs.card} total"
  return (qs, rows)

def explore : IO String := do
  let (qs, rows) ← componentQueries
  let components := (qs.val.map fun q ↦
    let v := componentValue q
    (Json.mkObj [("key",toJson (code q)),
      ("value",toJson [v.num,(v.den : ℤ)])]).compress).sort (· ≤ ·)
  let output := "{\"schema_version\":1,\"kind\":\"axiomatic_gw.plane_genus_two_components\"," ++
    "\"proof_status\":\"candidate_data\",\"rows\":[" ++ String.intercalate "," rows.toList ++
    "],\"components\":[" ++ String.intercalate "," components ++ "]}\n"
  (← IO.getStderr).putStrLn s!"exported {rows.size} rows and {components.length} component values"
  return output

/-- Component selections are performance hints; the cached-step preservation
theorem retains the original algorithm at every omitted key. -/
def ellipticSelections : IO String := do
  let (qs, _) ← componentQueries
  let ordered := (qs.val.map code).sort (· ≤ ·)
  let rows : Multiset String := qs.val.bind fun q ↦
    if hg : q.genus = 1 then
      if hp : ¬q.IsPrimary then
        if 3 ≤ q.totalPsi ∧ q.totalPsi ≤ q.insertions.card then
          let terms : RationalTerms Key :=
            ((PsiBoundaryExpansion.genusOneTerms (SurfaceGenusOne.extraCount q)).map
            fun t ↦ RationalTerms.scale t.1 (t.2.surfaceTerms .plane symbolic q.beta
              (SurfaceGenusOne.lowerAncestorPowers q hg hp)
              (q.orderedLabels ∘ SurfaceGenusOne.ancestorFrame q hg hp))).sum
          let needed : Finset Key := (terms.map fun t ↦ t.2.toFinset).sup
          let keys := (needed.val.map code).sort (· ≤ ·)
          {(Json.mkObj [("index", toJson (ordered.idxOf (code q))),
            ("component", toJson (code q)), ("keys", toJson keys)]).compress}
        else 0
      else 0
    else 0
  return "{\"schema_version\":1," ++
    "\"kind\":\"axiomatic_gw.plane_elliptic_component_selections\"," ++
    "\"proof_status\":\"cache_selection_hint\",\"rows\":[" ++
    String.intercalate "," (rows.sort (· ≤ ·)) ++ "]}\n"

end AxiomaticGW.PlaneGenusTwoComponentsExport

def main (args : List String) : IO Unit := do
  match args with
  | ["--elliptic-selections", path] =>
      IO.FS.writeFile path (← AxiomaticGW.PlaneGenusTwoComponentsExport.ellipticSelections)
  | [path] => IO.FS.writeFile path (← AxiomaticGW.PlaneGenusTwoComponentsExport.explore)
  | [] => IO.print (← AxiomaticGW.PlaneGenusTwoComponentsExport.explore)
  | _ => throw (IO.userError "expected an output path or --elliptic-selections and an output path")
