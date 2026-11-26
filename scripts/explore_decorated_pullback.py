#!/usr/bin/env python3
"""Compare the actual Lean signed expansion to admcycles in raw graph coordinates.

No relation quotient, intersection test, or zero oracle is used. The native
Lean export is supplementary evidence for independently kernel-proved general
identities. All twenty BP diagrams and six assignments are checked separately.
"""
import argparse
from collections import defaultdict
from copy import deepcopy
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require
from search_belorousski_pandharipande import key, relabel

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "environments/belorousski-pandharipande.json"
SOURCE_SHA256 = "5868b2f3ef1e5a45e6175b6349566b72c778f4ab028ef941b43498fd0ee8d1bc"


def signature(data):
    return key(dict(data, kappa=[[0, 0] for _ in data["genus"]]))


def explore(payload):
    from sage.all import QQ
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing, admcycles, stable_graph, tautological_ring
    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review Sage/admcycles pins")
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256,
            "The accepted BP source changed")
    source = json.loads(SOURCE.read_bytes())
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    data = json.loads(payload)
    require(data["schema_version"] == 1, "Unexpected Lean export version")
    extras = ["psi_square", "psi_product", "zero_power", "unmarked_zero", "loop_branches", "symmetric"]
    expected = {(f"bp_{i}_{e}", n) for i in range(20) for e in range(6) for n in (1, 2)}
    expected |= {(s, n) for s in extras for n in (1, 2)}
    observed = [(c["name"], c["additional_markings"]) for c in data["cases"]]
    require(len(observed) == len(expected) and set(observed) == expected, "Incomplete case coverage")

    def raw(ring, graph):
        n = len(graph["leg_vertices"])
        legs = [[] for _ in graph["genus"]]
        psi = {}
        for label, (v, p) in enumerate(zip(graph["leg_vertices"], graph["leg_psi"]), 1):
            legs[v].append(label)
            if p:
                psi[label] = p
        edges = []
        for e, (ends, powers) in enumerate(zip(graph["endpoints"], graph["half_psi"])):
            flags = (n + 2*e + 1, n + 2*e + 2)
            edges.append(flags)
            for h, v, p in zip(flags, ends, powers):
                legs[v].append(h)
                if p:
                    psi[h] = p
        return ring(StableGraph(graph["genus"], legs, edges), psi=psi)

    def coordinates(element, n):
        answer = defaultdict(QQ)
        for term in element._terms.values():
            graph = term.gamma
            for (kappa, psi), coefficient in zip(term.poly.monom, term.poly.coeff):
                require(all(not any(v) for v in kappa), "Unexpected kappa correction")
                graph_data = {"genus": list(map(int, graph.genera())),
                    "leg_vertices": [int(graph.vertex(i)) for i in range(1, n + 1)],
                    "leg_psi": [int(psi.get(i, 0)) for i in range(1, n + 1)],
                    "endpoints": [[int(graph.vertex(h)) for h in e] for e in graph.edges()],
                    "half_psi": [[int(psi.get(h, 0)) for h in e] for e in graph.edges()]}
                answer[signature(graph_data)] += coefficient
        return {k: v for k, v in answer.items() if v}

    def lean_coordinates(terms):
        answer = defaultdict(QQ)
        for t in terms:
            answer[signature(t["graph"])] += QQ(t["coefficient"])
        return {k: v for k, v in answer.items() if v}

    def digest(coords):
        serial = [[k, [int(v.numerator()), int(v.denominator())]] for k, v in sorted(coords.items())]
        return hashlib.sha256(json.dumps(serial, separators=(",", ":")).encode()).hexdigest()

    cases, saved, vector_checks = [], {}, 0
    totals = {n: [None, None] for n in (1, 2)}
    for c in data["cases"]:
        g, m, n = c["genus"], c["initial_markings"], c["additional_markings"]
        ring, target = (TautologicalRing(g, marks, moduli="st", base_ring=QQ) for marks in (m, m+n))
        original = raw(ring, c["original"])
        reference = original.forgetful_pullback(list(range(m+1, m+n+1)))
        exact = coordinates(reference, m+n)
        actual = lean_coordinates(c["terms"])
        require(actual == exact, f"Raw pullback mismatch: {c['name']}, n={n}")
        require(all(t["graph"]["codimension"] == c["original"]["codimension"] for t in c["terms"]),
                "Output codimension changed")
        manual = sum((QQ(t["coefficient"]) * raw(target, t["graph"]) for t in c["terms"]), target.zero())
        require(coordinates(manual, m+n) == actual, "Raw dictionary/admcycles construction mismatch")
        degree = c["original"]["codimension"]
        # Avoid constructing a large full degree-four basis for a sparse loop test.
        if degree <= 2:
            require(manual.vector(degree) == reference.vector(degree), "Raw vector mismatch")
            vector_checks += 1
        if c["name"].startswith("bp_"):
            _, i, e = c["name"].split("_"); i, e = int(i), int(e)
            inverse = [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)][e]
            held = source["published_terms"][i]
            require(signature(c["original"]) == signature(relabel(held["graph"], inverse)),
                    "Lean original does not match the held published term")
            q = QQ(held["coefficient"][0]) / held["coefficient"][1] / held["automorphism"]
            if totals[n][0] is None:
                totals[n] = [target.zero(), target.zero()]
            totals[n][0] += q * manual
            totals[n][1] += q * reference
        cases.append({"name": c["name"], "additional_markings": n,
                      "signed_terms": len(c["terms"]), "raw_support": len(exact),
                      "raw_coordinate_sha256": digest(exact), "raw_equal": True})
        saved[c["name"], n] = (c, exact)
    totals_report = []
    for n, (manual, reference) in totals.items():
        require(manual.vector(2) == reference.vector(2), "Full weighted BP pullback mismatch")
        coords = coordinates(manual, 3+n)
        require(coords, "The BP request disappeared in the free raw frame")
        totals_report.append({"additional_markings": n, "raw_support": len(coords),
                              "raw_coordinate_sha256": digest(coords)})

    rejected = []
    def negative(name, case, mutation):
        c, exact = saved[case, 1]
        terms = deepcopy(c["terms"])
        mutation(terms)
        require(lean_coordinates(terms) != exact, f"Bad expansion was accepted: {name}")
        rejected.append(name)
    negative("omit_all_rational_tails", "psi_square", lambda ts: ts.__setitem__(slice(None),
             [t for t in ts if t["coefficient"] > 0]))
    def wrong_power_coefficient(ts):
        tail = next(t for t in ts if t["coefficient"] < 0)
        tail["coefficient"] = -2
    negative("use_minus_power_instead_of_minus_one", "psi_square", wrong_power_coefficient)
    def wrong_node_branch(ts):
        positive = next(t for t in ts if t["coefficient"] > 0 and any(map(any, t["graph"]["half_psi"])))
        edge = next(p for p in positive["graph"]["half_psi"] if any(p))
        edge.reverse()
    negative("swap_genus_two_node_branch", "bp_1_0", wrong_node_branch)
    negative("discard_repeated_symmetric_placement", "symmetric", lambda ts: ts.pop())
    require(list(saved["symmetric", 1][1].values()) == [2], "Lost symmetric multiplicity")
    require(len(saved["zero_power", 1][0]["terms"]) == 1, "Zero powers acquired a correction")
    return {"schema_version": 1, "status": "passed_raw_comparison", "cases": cases,
        "full_bp": totals_report, "cases_checked": len(cases), "raw_vector_checks": vector_checks + 2,
        "negative_expansions_rejected": rejected, "original_bp_source_sha256": SOURCE_SHA256,
        "lean_payload_sha256": hashlib.sha256(payload).hexdigest(), "lean_payload_bytes": len(payload),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "environment": {"sage": version, "admcycles": "1.4", "python": platform.python_version(),
                        "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                                   for m in (admcycles, stable_graph, tautological_ring)},
        "cache_ephemeral": True, "online_lookup": False,
        "scope": "Actual native Lean terms equal admcycles pullbacks before any tautological quotient. "
                 "General class soundness is separately kernel-proved from named primitive geometry; "
                 "this diagnostic proves no geometric vanishing or numerical GW value."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-input", type=Path)
    args = parser.parse_args()
    if args.lean_input:
        payload = args.lean_input.read_bytes()
    else:
        subprocess.run(["lake", "build", "decoratedPullback"], cwd=ROOT, check=True, stdout=sys.stderr)
        payload = subprocess.check_output([str(ROOT / ".lake/build/bin/decoratedPullback")], cwd=ROOT)
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-decorated-pullback-") as temporary:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(temporary) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        print(json.dumps(explore(payload), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
