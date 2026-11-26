#!/usr/bin/env python3
"""Emit the fixed native L24 comparison program using the existing JSON codecs.

This produces an untrusted diagnostic program, not a proof or a new GW seed.
The serialization helpers are reused verbatim from the pinned existing BP
exporter, so this script does not add a competing query or coefficient format.
Compile the emitted program with Lake, then compare
its complete payload with explore_surface_l24.py in the pinned Sage environment.
"""
import argparse
import hashlib
from pathlib import Path

from export_admcycles_certificate import require

ROOT = Path(__file__).resolve().parents[1]
CODEC_SOURCE = ROOT / 'scripts/SurfaceBP.lean'
CODEC_SHA256 = '517b9cbdd9817728ad4f0762c77d178daf6169e1c9396b1653b7cae91cfc69e4'

BODY = r'''/-- Collect small component sets incrementally, before repeated terms accumulate. -/
def cacheQueries {X : SurfaceTarget} (raw : RationalTerms (SurfaceAncestorKey X)) :
    Finset (SurfaceAncestorKey X) :=
  (raw.map fun t ↦ t.2.toFinset.filter (fun q ↦ q.genus ≤ 1)).sup

/-- The incremental collection preserves every distinct lower-genus query. -/
theorem cacheQueries_eq {X : SurfaceTarget} (raw : RationalTerms (SurfaceAncestorKey X)) :
    cacheQueries raw = ((raw.bind Prod.snd).filter (fun q ↦ q.genus ≤ 1)).toFinset := by
  induction raw using Multiset.induction_on with
  | empty => rfl
  | cons t s ih =>
    simpa only [cacheQueries, Multiset.map_cons, Multiset.sup_cons,
      Multiset.cons_bind, Multiset.filter_add, Multiset.toFinset_add,
      Multiset.toFinset_filter, Finset.sup_eq_union] using congrArg
        (fun u ↦ t.2.toFinset.filter (fun q ↦ q.genus ≤ 1) ∪ u) ih

def caseJSON (name : String) (X : SurfaceTarget) (beta : X.Curve) (n : ℕ)
    (a : Fin 4 → SurfaceBasisLabel X) : String :=
  let labels := SurfaceGenusZero.pointLabels a n
  let raw := L24Relation.surfaceTerms X (symbolicVertex X) n beta 0 labels
  let queries := cacheQueries raw
  let reduced := L24Relation.genusTwoTermsCached X queries n beta 0 labels
  let low := queries.val.map fun q ↦
    (Json.mkObj [("query", queryJSON q), ("value", ratJSON
      (SurfaceGenusOne.componentValue X (SurfaceGenusOne.ancestorValue X) q))]).compress
  let head := (Json.mkObj [("name", toJson name), ("blowups", toJson X.blowups),
    ("curve", toJson ((List.finRange (X.blowups + 1)).map beta)),
    ("additional_markings", toJson n),
    ("labels", toJson ((List.finRange 4).map (fun i ↦ labelCode (a i))))]).compress
  head.dropEnd 1 |>.toString ++ ",\"symbolic_terms\":" ++ termsJSON raw ++
    ",\"genus_two_terms\":" ++ termsJSON reduced ++ ",\"lower_values\":[" ++
    String.intercalate "," (low.sort (· ≤ ·)) ++ "]}"

end AxiomaticGW.SurfaceL24Export
open AxiomaticGW SurfaceL24Export

def main (args : List String) : IO Unit := do
  let jobs : List (String × (Unit → String)) := [
    ("p2_zero_HH11", fun _ ↦ caseJSON "p2_zero_HH11" .plane ![0] 0
      ![.hyperplane, .hyperplane, .unit, .unit]),
    ("p2_line_HHHP", fun _ ↦ caseJSON "p2_line_HHHP" .plane ![1] 0
      ![.hyperplane, .hyperplane, .hyperplane, .point]),
    ("p2_line_HHHH_p", fun _ ↦ caseJSON "p2_line_HHHH_p" .plane ![1] 1
      (fun _ ↦ .hyperplane)),
    ("f1_E_EEE1", fun _ ↦ caseJSON "f1_E_EEE1" .hirzebruchOne ![1,0] 0
      ![.exceptional 0, .exceptional 0, .exceptional 0, .unit]),
    ("f1_F_EHHH", fun _ ↦ caseJSON "f1_F_EHHH" .hirzebruchOne ![0,1] 0
      ![.exceptional 0, .hyperplane, .hyperplane, .hyperplane]),
    ("bl2_E1_E1E1E11", fun _ ↦ caseJSON "bl2_E1_E1E1E11" .blowupTwo ![1,0,0] 0
      ![.exceptional 0, .exceptional 0, .exceptional 0, .unit]),
    ("bl2_E2_E1E1E11", fun _ ↦ caseJSON "bl2_E2_E1E1E11" .blowupTwo ![0,1,0] 0
      ![.exceptional 0, .exceptional 0, .exceptional 0, .unit]),
    ("bl2_L_E1E2H1", fun _ ↦ caseJSON "bl2_L_E1E2H1" .blowupTwo ![0,0,1] 0
      ![.exceptional 0, .exceptional 1, .hyperplane, .unit]),
    ("bl2_E1E2_E1E1E2E2", fun _ ↦ caseJSON "bl2_E1E2_E1E1E2E2" .blowupTwo ![1,1,0] 0
      ![.exceptional 0, .exceptional 0, .exceptional 1, .exceptional 1])]
  let stderr ← IO.getStderr
  let mut cases := []
  for (name, run) in jobs do
    if args.isEmpty || args.contains name then
      stderr.putStrLn s!"Expanding {name}"
      cases := cases ++ [run ()]
  IO.println ("{\"schema_version\":1,\"cases\":[" ++ String.intercalate "," cases ++ "]}")
'''


def generate():
    raw = CODEC_SOURCE.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == CODEC_SHA256, 'Changed held query codecs')
    text = raw.decode()
    start = 'namespace AxiomaticGW.SurfaceBPExport\n'
    end = '/-- Export both stages'
    require(text.count(start) == 1 and text.count(end) == 1, 'Ambiguous codec boundaries')
    helpers = text.split(start, 1)[1].split(end, 1)[0]
    return ('/-\nCopyright (c) 2026 JMA. All rights reserved.\n'
            'Released under Apache 2.0 license as described in the file LICENSE.\n'
            'Authors: JMA\n-/\nmodule\n\n'
            'public import AxiomaticGW.Surfaces.L24Terms\n\n'
            '/-!\n# Diagnostic export of complete L24 surface equations\n\n'
            'Generated by `scripts/export_surface_l24.py` using the existing BP codecs.\n'
            'The output is candidate data; the companion `Surfaces.L24` theorems supply\n'
            'conditional soundness. No numerical value or native result is a proof.\n-/\n\n'
            '@[expose] public section\nset_option maxRecDepth 20000\n\n'
            'namespace AxiomaticGW.SurfaceL24Export\n' + helpers + '\n' + BODY)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = generate()
    if args.check:
        require(args.output.read_text() == source, 'Stored diagnostic program differs')
    else:
        args.output.write_text(source)


if __name__ == '__main__':
    main()
