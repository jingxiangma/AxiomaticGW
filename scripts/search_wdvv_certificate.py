#!/usr/bin/env python3
"""Generate marked raw boundary candidates and search a fixed Keel-row consequence.

Run with Sage 10.9 / admcycles 1.4 Python. The boundary relation is the
explicit geometric input from Keel, Section 4, Theorem 1, Part I(2).
Sage searches an exact row witness; no zero flag supplies geometric validity.
Lean independently fixes the graph frame, rows, normalization, and request.
"""

import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import sys
import tempfile

from export_admcycles_certificate import require


def run_search():
    # main() isolates all caches before these imports.
    from sage.all import QQ, matrix, vector
    from sage.version import version
    from admcycles import TautologicalRing
    from admcycles import admcycles, stable_graph, tautological_ring

    require(version == "10.9", "Review the Sage pin before regenerating")
    require(importlib.metadata.version("admcycles") == "1.4", "Review the admcycles pin")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")

    def rational(q):
        q = QQ(q)
        return [int(q.numerator()), int(q.denominator())]

    ring = TautologicalRing(0, 4, moduli="st", base_ring=QQ)
    channels = [ring.separable_boundary_divisor(0, pair)
                for pair in ((1, 2), (1, 3), (1, 4))]
    graphs, raw_vectors, raw_indices = [], [], []
    for index, channel in enumerate(channels):
        # The pinned TautologicalClass documents its decstratum term storage.
        # This reader is outside the trust boundary; replay checks its result.
        require(len(channel._terms) == 1, "Expected one raw boundary term")
        term = next(iter(channel._terms.values()))
        require(len(term.poly.monom) == 1 and list(term.poly.coeff) == [1],
                "Expected one monomial with raw coefficient one")
        kappa, psi = term.poly.monom[0]
        graph = term.gamma
        require(all(not any(row) for row in kappa) and not any(psi.values()),
                "Boundary constructor introduced a decoration")
        endpoints = [[int(graph.vertex(branch)) for branch in edge] for edge in graph.edges()]
        graphs.append({
            "index": index, "genus": [int(g) for g in graph.genera()],
            "leg_vertices": [int(graph.vertex(s)) for s in range(1, 5)],
            "endpoints": endpoints, "kappa": [[0] for _ in graph.genera()],
            "leg_psi": [0] * 4, "half_psi": [[0, 0] for _ in endpoints],
        })
        raw = channel.vector(1)
        selected = [j for j, q in enumerate(raw) if q]
        require(len(selected) == 1 and raw[selected[0]] == 1,
                "Boundary raw vector is not a unit coordinate")
        require(ring.from_vector(raw, 1).vector(1) == raw, "Raw vector round-trip failed")
        raw_vectors.append([rational(q) for q in raw])
        raw_indices.append(selected[0])
    require(len(set(raw_indices)) == 3, "External labels were identified")

    # The request is specified independently; these are named Keel generator rows.
    rows = matrix(QQ, [[1, -1, 0], [0, 1, -1]])
    requested = vector(QQ, [1, 0, -1])
    witness = rows.solve_left(requested)
    require(witness * rows == requested, "Invalid searched witness")
    return {
        "schema_version": 1, "frame": "wdvv_mbar_0_4_v1", "locus": "full_stable",
        "genus": 0, "markings": [0, 1, 2, 3], "codimension": 1,
        "normalization": "raw_gluing_pushforward",
        "source_label_map": [[1, 0], [2, 1], [3, 2], [4, 3]],
        "relation_ids": ["keel_01_23_minus_02_13", "keel_02_13_minus_03_12"],
        "relation_source": "10.1090/S0002-9947-1992-1034665-0; Section 4, Theorem 1, I(2)",
        "graphs": graphs, "column_factors": [[1, 1]] * 3,
        "rows": [[rational(q) for q in row] for row in rows],
        "requested": [rational(q) for q in requested],
        "witness": [rational(q) for q in witness],
        "environment": {"sage": version, "admcycles": "1.4",
                        "python": platform.python_version(), "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name:
            hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (admcycles, stable_graph, tautological_ring)},
        "exploration": {"raw_vectors": raw_vectors, "raw_column_indices": raw_indices,
                        "cache_ephemeral": True, "online_lookup": False},
        "scope": "Candidate marked raw graphs and exact searched witness; geometric boundary "
                 "class equality is an explicit Lean hypothesis, not a Sage conclusion.",
    }


def main():
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-wdvv-search-") as temporary:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(temporary) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        print(json.dumps(run_search(), indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"WDVV search failed: {error}", file=sys.stderr)
        sys.exit(1)
