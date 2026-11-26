/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.PlaneGenusTwoRemainder

/-!
# Plane BP coefficients one degree above the requested invariants

Native output is exploration data. Effective-remainder recursion, signed point
compression and coefficient extraction have universal correctness theorems;
each numerical row still requires its own kernel replay.
The fixed requests include all four published marking choices, the absent
input-class columns, and a second positive degree.
-/

@[expose] public section
set_option maxRecDepth 20000

namespace AxiomaticGW.GenusTwoShiftedExport
open Lean

/-- The plane primary, hyperplane descendant and point descendant, in that order. -/
def columns (d : ℕ) : List (SurfaceQuery .plane) :=
  [SurfaceQuery.points .plane 2 ![d] (3 * d + 1),
    SurfaceFirstDescendant.query 2 ![d] .hyperplane (3 * d),
    SurfaceFirstDescendant.query 2 ![d] .point (3 * d - 1)]

/-- Existing surface exchange codes, restricted to the plane. -/
def labelCode : SurfaceBasisLabel .plane → ℕ
  | .unit => 0
  | .hyperplane => 1
  | .point => 2
  | .exceptional i => Fin.elim0 i

/-- Preserve the complete column request, including sorted insertion powers. -/
def queryJSON (q : SurfaceQuery .plane) : Json :=
  Json.mkObj [("genus", toJson q.genus), ("curve", toJson [q.beta 0]),
    ("insertions", toJson ((q.insertions.map fun i ↦
      [labelCode i.label, i.psi]).mergeSort (· ≤ ·)))]

/-- A fixed full request and its three exact coefficients. -/
def row (name : String) (source targetDegree n : ℕ)
    (a : Fin 3 → SurfaceBasisLabel .plane) : Json :=
  let queries := columns targetDegree
  let values := queries.map fun q ↦
    BelorousskiPandharipande.planePointCoefficientByRemainder n source a (.inr q)
  Json.mkObj [("name", toJson name), ("source_curve", toJson [source]),
    ("variable_curve", toJson [targetDegree]), ("additional_markings", toJson n),
    ("labels", toJson ((List.finRange 3).map fun i ↦ labelCode (a i))),
    ("columns", toJson (queries.map queryJSON)),
    ("coefficients", toJson (values.map fun q ↦ [q.num, (q.den : ℤ)]))]

end AxiomaticGW.GenusTwoShiftedExport

open AxiomaticGW GenusTwoShiftedExport Lean

def main (args : List String) : IO Unit := do
  let jobs : List (String × (Unit → Json)) := [
    ("d1_HHH", fun _ ↦ row "d1_HHH" 2 1 5 ![.hyperplane, .hyperplane, .hyperplane]),
    ("d1_HHP", fun _ ↦ row "d1_HHP" 2 1 4 ![.hyperplane, .hyperplane, .point]),
    ("d1_HPP", fun _ ↦ row "d1_HPP" 2 1 3 ![.hyperplane, .point, .point]),
    ("d1_PPP", fun _ ↦ row "d1_PPP" 2 1 2 ![.point, .point, .point]),
    ("same_d2_HHP", fun _ ↦ row "same_d2_HHP" 2 2 4 ![.hyperplane, .hyperplane, .point]),
    ("same_d2_HPP", fun _ ↦ row "same_d2_HPP" 2 2 3 ![.hyperplane, .point, .point]),
    ("same_d2_PPP", fun _ ↦ row "same_d2_PPP" 2 2 2 ![.point, .point, .point]),
    ("d2_HHP", fun _ ↦ row "d2_HHP" 3 2 7 ![.hyperplane, .hyperplane, .point]),
    ("d2_HPP", fun _ ↦ row "d2_HPP" 3 2 6 ![.hyperplane, .point, .point]),
    ("d2_PPP", fun _ ↦ row "d2_PPP" 3 2 5 ![.point, .point, .point])]
  let stderr ← IO.getStderr
  let mut cases := []
  for (name, run) in jobs do
    if args.isEmpty || args.contains name then
      stderr.putStrLn s!"Shifted BP: {name}"
      cases := cases ++ [run ()]
  IO.println (Json.mkObj [("schema_version", toJson (1 : ℕ)), ("cases", toJson cases)]).compress
