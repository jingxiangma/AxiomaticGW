/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Surfaces.PlaneGenusTwoCertificate
import AxiomaticGW.Surfaces.PlaneGenusTwoScalarParts

/-!
# Exact exploration of the complete plane genus-two recursion

Run with `lake env lean --run`, a degree bound and optionally an output path.
The default bound is four, the fixed primary and first-descendant benchmark. Results are
candidates: the finite-table checker must separately certify every row.
Coefficients multiplying zero earlier values are omitted, as in the proved
scalar evaluator. All three full requests and every candidate zero remain.
The optional `--parts` flag additionally exports every original diagram and
marking contribution for componentwise kernel replay.
-/

set_option maxRecDepth 20000

namespace AxiomaticGW.PlaneGenusTwoScalarExport
open Lean BelorousskiPandharipande

/-- Exact rational arithmetic is serialized as numerator and positive denominator. -/
def rationalJSON (q : ℚ) : Json := toJson [q.num, (q.den : ℤ)]

/-- Plane labels use the same codes as the existing surface exchange. -/
def labelCode : SurfaceBasisLabel .plane → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .point => 2
  | .exceptional i => Fin.elim0 i

/-- Preserve the original order, full class and every descendant power. -/
def queryJSON (q : SurfaceQuery .plane) : Json :=
  Json.mkObj [("genus", toJson q.genus), ("curve", toJson [q.beta 0]),
    ("insertions", toJson (q.insertions.map fun t ↦ [labelCode t.label, t.psi]))]

/-- Evaluate all rows through the held degree bound using the full scalar remainders. -/
def explore (bound : ℕ) (parts : Bool := false) : IO Json := do
  let stderr ← IO.getStderr
  let mut values : Array (Fin 3 → ℚ) := #[![0, -1 / 960, 0]]
  let mut rows : Array Json := #[]
  for d in [1:bound + 1] do
    let mut remainders : Array ℚ := #[]
    let mut equations : Array Json := #[]
    for i in List.finRange 3 do
      stderr.putStrLn s!"Plane genus two: degree {d}, row {i.val}"
      let constantParts := if parts then
        (List.finRange 16).map fun k ↦
          (List.finRange 6).map fun e ↦ planeShiftedConstantPart d i k e
        else []
      let constant := if parts then (constantParts.map List.sum).sum
        else planeShiftedConstantFast d i
      let mut rem := constant
      let mut coefficients : Array Json := #[]
      for b in [:d] do
        for j in List.finRange 3 do
          if values[b]! j != 0 then
            let coefficientParts := if parts then
              (List.finRange 4).map fun k ↦
                (List.finRange 6).map fun e ↦ planeEarlierCoefficientPart d i b j k e
              else []
            let c := if parts then (coefficientParts.map List.sum).sum
              else planeEarlierCoefficient d i b j
            rem := rem + c * values[b]! j
            let fields := [("degree", toJson b), ("family", toJson j.val),
              ("coefficient", rationalJSON c)]
            let fields := if parts then fields ++
              [("parts", toJson (coefficientParts.map (List.map rationalJSON)))] else fields
            coefficients := coefficients.push (Json.mkObj fields)
      remainders := remainders.push rem
      let fields := [("family", toJson i.val),
        ("constant", rationalJSON constant), ("earlier_coefficients", toJson coefficients),
        ("remainder", rationalJSON rem)]
      let fields := if parts then fields ++
        [("constant_parts", toJson (constantParts.map (List.map rationalJSON)))] else fields
      equations := equations.push (Json.mkObj fields)
    let next := planeShiftedSolve d (fun i ↦ -remainders[i.val]!)
    rows := rows.push (Json.mkObj [("degree", toJson d),
      ("requests", toJson ((List.finRange 3).map fun i ↦ queryJSON (planeCanonicalQueries d i))),
      ("values", toJson ((List.finRange 3).map fun i ↦ rationalJSON (next i))),
      ("equations", toJson equations)])
    stderr.putStrLn s!"Plane genus two: degree {d}, values {(List.finRange 3).map next}"
    values := values.push next
  return Json.mkObj [("schema_version", toJson (1 : ℕ)),
    ("kind", toJson (if parts then "axiomatic_gw.plane_genus_two_scalar_parts"
      else "axiomatic_gw.plane_genus_two_scalar")),
    ("bound", toJson bound), ("initial", toJson ((List.finRange 3).map fun i ↦
      rationalJSON ((![0, -1 / 960, 0] : Fin 3 → ℚ) i))), ("rows", toJson rows)]

end AxiomaticGW.PlaneGenusTwoScalarExport

open AxiomaticGW.PlaneGenusTwoScalarExport

def main (args : List String) : IO Unit := do
  let parts := args.contains "--parts"
  let args := args.filter (· != "--parts")
  let some bound := (args.headD "4").toNat? | throw (IO.userError "Expected a degree bound")
  let report ← explore bound parts
  match args[1]? with
  | some output => IO.FS.writeFile (System.FilePath.mk output) (report.pretty ++ "\n")
  | none => IO.println report.compress
