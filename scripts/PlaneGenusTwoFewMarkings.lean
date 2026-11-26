/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests
import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine
import AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate

/-!
# Complete plane genus-two few-marking exploration

Evaluate the proved complete frame using the descendant algorithm and the
accepted degree-one canonical table. The emitted numbers are candidates;
each still needs kernel replay. No localization values enter this computation.
-/

set_option maxRecDepth 20000

namespace AxiomaticGW.PlaneFewMarkingExport
open Lean BelorousskiPandharipande

private def labelName : SurfaceBasisLabel .plane → String
  | .unit => "unit"
  | .hyperplane => "H"
  | .point => "pt"
  | .exceptional i => Fin.elim0 i

private def caseJSON (q : SurfaceQuery .plane) (v : ℚ) : Json :=
  Json.mkObj [("target", toJson "X0"), ("genus", toJson q.genus),
    ("class", toJson [q.beta 0]),
    ("powers", toJson (q.insertions.map SurfaceInsertion.psi)),
    ("labels", toJson (q.insertions.map fun t ↦ labelName t.label)),
    ("ordinary", toJson [v.num, (v.den : ℤ)])]

def explore : IO Json := do
  let stderr ← IO.getStderr
  let mut cases : Array Json := #[]
  for i in List.finRange 48 do
    let q := GenusTwoPlaneFewMarkingRequests.requests i
    stderr.putStrLn s!"Plane few markings {cases.size + 1}/48: {repr q.insertions}"
    stderr.flush
    let some value := planeQueryValueWith? GenusTwoPlaneLine.values q
      | throw (IO.userError "The fixed frame unexpectedly contains an unsupported genus")
    let result := caseJSON q value
    cases := cases.push result
    stderr.putStrLn result.compress
    stderr.flush
  return Json.mkObj [("schema_version", toJson (1 : ℕ)),
    ("kind", toJson "axiomatic_gw.plane_genus_two_few_markings"),
    ("positive_energy_bound", toJson (4 : ℕ)),
    ("maximum_markings", toJson (2 : ℕ)), ("cases", toJson cases)]

end AxiomaticGW.PlaneFewMarkingExport

def main (args : List String) : IO Unit := do
  let report ← AxiomaticGW.PlaneFewMarkingExport.explore
  match args.head? with
  | some output => IO.FS.writeFile (System.FilePath.mk output) (report.pretty ++ "\n")
  | none => IO.println report.compress
