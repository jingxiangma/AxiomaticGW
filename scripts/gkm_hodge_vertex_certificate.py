#!/usr/bin/env python3
"""Export an offline Lean check of all genus-two vertex signatures in a reduced exploration."""
import argparse
import hashlib
import json
from pathlib import Path

from check_gkm_inputs import integer, unique_object
from export_admcycles_certificate import rational, rational_text
from export_gkm_inputs import PIN, require
from gkm_hodge_reduction import KIND, SEEDS
from gkm_research_query import frame
from gkm_three_point_descendants import read_report
from gw_query import validate


def rows(data):
    result = {}
    for row in data:
        ls = tuple(map(integer, row["lambda"]))
        psis = tuple(map(integer, row["psi"]))
        require(len(ls) == 2 and 0 <= ls[0] <= ls[1] <= 2 and all(k >= 0 for k in psis)
                and tuple(sorted(psis)) == psis, "Invalid normalized Hodge signature")
        require((ls, psis) not in result, "Duplicate Hodge signature")
        result[ls, psis] = rational(row["value"])
    return result


def emit(raw, *, exceptional_cubic=False):
    data = json.loads(raw, object_pairs_hook=unique_object)
    require(data["kind"] == KIND and data["source"] == json.loads(PIN.read_bytes())
            and data["environment"] == {"sage": "10.9", "admcycles": "1.4"}, "Wrong origin")
    query, _, _ = validate(data["query"])
    require(query["genus"] == 2, "Expected a genus-two surface query")
    read_report(json.dumps(data["localization"]), requests=frame(query), genus=2, kind=KIND)
    seeds, vertices = rows(data["seeds"]), rows(data["vertices"])
    require(set(seeds) == set(SEEDS), "Expected all eight reduced Hodge seeds")
    require(vertices, "This report has no genus-two vertex integrals")
    if exceptional_cubic:
        require(query == {"target": "X2", "genus": 2, "class": [1, 0, 0], "insertions": [["E1", 3]]},
                "The cubic exceptional fixture requires the original ordered request")

    def key(ls, psis):
        return f"({ls[0]}, {ls[1]}, {list(psis)})"

    keys = ",\n    ".join(key(*k) for k in seeds)
    cases = "\n".join(f"  | {key(ls, psis)} => {rational_text(v)}" for (ls, psis), v in seeds.items())
    values = ",\n    ".join(f"({ls[0]}, {ls[1]}, {list(psis)}, {rational_text(v)})"
                            for (ls, psis), v in vertices.items())
    namespace = "ExceptionalGenusTwoVertexValues" if exceptional_cubic else "HodgeVertexCertificate"
    header = "module\n\npublic import" if exceptional_cubic else "import"
    scope = "@[expose] public section\n" if exceptional_cubic else ""
    audit = "" if exceptional_cubic else "#print axioms vertex_sound\n"
    return f"""/- Computed genus-two vertex integrals for {query['target']} in class {query['class']}.
Ordered insertions: {query['insertions']}.
Report SHA256: {hashlib.sha256(raw).hexdigest()}.
The eight seed values come from admcycles. The geometric interpretation uses the
explicit forgetful and dimension equations. The enclosing graph sum is outside this certificate. -/
{header} AxiomaticGW.GKM.GenusTwoVertexHodgeReduction

{scope}namespace AxiomaticGW.GKM.{namespace}
open GenusTwoVertexHodgeReduction

/-- The eight literal seed integrals in the native admcycles ledger. -/
def seed (k : ↥seeds) : ℚ :=
  match k.val with
{cases}
  | _ => 0

/-- The supplied seed keys span the complete reduced vertex domain. -/
theorem seed_support : seeds = ([{keys}] : List (ℕ × ℕ × List ℕ)).toFinset := by decide +kernel

/-- Every distinct marked Hodge integral consumed during the held graph sum. -/
def vertices : List (Fin 3 × Fin 3 × List ℕ × ℚ) :=
  [{values}]

/-- Compare one actual input and value with the checked vertex recurrence. -/
def agrees (r : Fin 3 × Fin 3 × List ℕ × ℚ) : Bool :=
  if h : r.1 ≤ r.2.1 then decide (evaluate seed r.1 r.2.1 h r.2.2.1 = r.2.2.2) else false

theorem checked : vertices.all agrees = true := by decide +kernel

theorem vertex_sound (i j : Fin 3) (hij : i ≤ j) (p : List ℕ) (v : ℚ)
    (hr : (i, j, p, v) ∈ vertices) (V : List ℕ → ℚ) (h : Recurrences i j V)
    (hs : ∀ ps (hk : ((i : ℕ), (j : ℕ), ps) ∈ seeds), seed ⟨_, hk⟩ = V ps) :
    V p = v := by
  have hv := List.all_eq_true.mp checked _ hr
  simpa only [agrees, dif_pos hij, decide_eq_true_eq, evaluate_sound seed i j hij V h hs] using hv

{audit}end AxiomaticGW.GKM.{namespace}
"""


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--exceptional-cubic", action="store_true", help="Emit the importable fixed E1 fixture")
    args = parser.parse_args()
    source = emit(args.report.read_bytes(), exceptional_cubic=args.exceptional_cubic)
    if args.check:
        require(args.output.read_text() == source, "Saved Lean certificate differs from native inputs")
    else:
        args.output.write_text(source)
