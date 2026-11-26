#!/usr/bin/env python3
"""Check undecorated Getzler forgetful pullbacks in pinned Sage/admcycles.

This compares raw strata coordinates, before imposing any tautological relation.
It is exploration evidence for the next Lean construction, not a certificate of
geometric vanishing. Decorated pullbacks require additional psi/kappa terms.
"""

import hashlib
import importlib.metadata
from itertools import product
import json
import os
from pathlib import Path
import platform
import sys
import tempfile

from export_admcycles_certificate import require


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "environments/getzler-candidate-osx-arm64.json"
SOURCE_SHA256 = "ccd8a8f941e9d2d503ec91e29b2be527bf0c91ce111599e6ec56118f6994ecb7"


def explore():
    from sage.all import QQ
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing
    from admcycles import admcycles, stable_graph, tautological_ring

    require(version == "10.9", "Review the Sage pin")
    require(importlib.metadata.version("admcycles") == "1.4", "Review the admcycles pin")
    source_bytes = SOURCE.read_bytes()
    require(hashlib.sha256(source_bytes).hexdigest() == SOURCE_SHA256,
            "The held Getzler candidate changed")
    source = json.loads(source_bytes)
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")

    def raw_graph(data, additions=()):
        """Rebuild incidence independently, reserving new labels before node flags."""
        markings = data["leg_vertices"] + list(additions)
        legs = [[] for _ in data["genus"]]
        for label, vertex in enumerate(markings, 1):
            legs[vertex].append(label)
        edges = []
        for edge, endpoints in enumerate(data["endpoints"]):
            flags = (len(markings) + 1 + 2 * edge, len(markings) + 2 + 2 * edge)
            edges.append(flags)
            for flag, vertex in zip(flags, endpoints):
                legs[vertex].append(flag)
        return StableGraph(data["genus"], legs, edges)

    def rational(q):
        return [int(QQ(q).numerator()), int(QQ(q).denominator())]

    def sparse(raw, degree=2):
        return {int(i): q for i, q in enumerate(raw.vector(degree)) if q}

    def unit_index(raw):
        coordinates = sparse(raw)
        require(len(coordinates) == 1 and list(coordinates.values()) == [1],
                "Expected one raw unit coordinate")
        return next(iter(coordinates))

    ring = TautologicalRing(1, 4, moduli="st", base_ring=QQ)
    original = [ring(raw_graph(data)) for data in source["graphs"]]
    rows = [QQ(n) / d for n, d in source["rows"][0]]
    requested = [QQ(n) / d for n, d in source["requested"]]
    witness = QQ(source["witness"][0][0]) / source["witness"][0][1]
    cases = []
    for extra in (1, 2):
        target = TautologicalRing(1, 4 + extra, moduli="st", base_ring=QQ)
        forgotten = list(range(5, 5 + extra))
        expanded_row = target.zero()
        expanded_request = target.zero()
        all_indices, columns = set(), []
        for data, raw, coefficient, claim in zip(source["graphs"], original, rows, requested):
            manual = target.zero()
            indices = []
            for assignment in product(range(len(data["genus"])), repeat=extra):
                added = target(raw_graph(data, assignment))
                index = unit_index(added)
                require(index not in all_indices, "Unexpected coincident Getzler marking placement")
                all_indices.add(index)
                indices.append(index)
                manual += added
            pulled = raw.forgetful_pullback(forgotten)
            require(pulled.vector(2) == manual.vector(2), "Raw graph pullback mismatch")
            require(set(sparse(pulled).values()) == {1}, "Changed raw marking multiplicity")
            expanded_row += coefficient * manual
            expanded_request += claim * manual
            columns.append({"source_column": data["index"], "vertices": len(data["genus"]),
                            "placements": len(indices), "raw_indices": indices})
        expected = 25 * 3**extra + 8 * 2**extra
        require(len(all_indices) == expected, "Incomplete marked support")
        original_row = sum((q * raw for q, raw in zip(rows, original)), ring.zero())
        original_request = sum((q * raw for q, raw in zip(requested, original)), ring.zero())
        require(expanded_row.vector(2) == original_row.forgetful_pullback(forgotten).vector(2),
                "Pullback changed source relation coefficients")
        require(expanded_request.vector(2) ==
                original_request.forgetful_pullback(forgotten).vector(2),
                "Pullback changed held request coefficients")
        require(witness * expanded_row.vector(2) == expanded_request.vector(2),
                "The original exact witness did not transport")
        require(len(sparse(expanded_row)) == expected, "Source row unexpectedly cancelled")
        require(len(sparse(expanded_request)) == expected, "Held request unexpectedly cancelled")
        # This deliberately does not ask admcycles whether the relation vanishes.
        cases.append({"additional_markings": extra, "raw_support": expected,
                      "columns": columns, "source_row_nonzero": True,
                      "held_request_nonzero": True, "raw_equalities_checked": True,
                      "witness": rational(witness)})

    # Vertex symmetry matters outside the marked Getzler frame: both placements
    # give the same raw graph, so multiplicity two must survive consolidation.
    symmetric_ring = TautologicalRing(2, 0, moduli="st", base_ring=QQ)
    symmetric = symmetric_ring(StableGraph([1, 1], [[1], [2]], [(1, 2)]))
    symmetric_pullback = symmetric.forgetful_pullback([1])
    symmetric_coordinates = sparse(symmetric_pullback, 1)
    require(len(symmetric_coordinates) == 1 and list(symmetric_coordinates.values()) == [2],
            "Vertex-orbit multiplicity was lost")

    # The vertex-only rule does not extend to decorated classes: psi pullback
    # subtracts a rational-tail term. Record a countercheck to prevent that reuse.
    psi_source = TautologicalRing(1, 2, moduli="st", base_ring=QQ)
    psi_target = TautologicalRing(1, 3, moduli="st", base_ring=QQ)
    psi_correction = psi_source.psi(2).forgetful_pullback([3]) - psi_target.psi(2)
    correction_coordinates = sparse(psi_correction, 1)
    require(len(correction_coordinates) == 1 and list(correction_coordinates.values()) == [-1],
            "Expected the nonzero negative rational-tail correction")

    return {
        "schema_version": 1, "status": "passed_exploration_checks",
        "source": str(SOURCE.relative_to(ROOT)), "source_sha256": SOURCE_SHA256,
        "normalization": "raw_gluing_pushforward", "locus": "full_stable",
        "environment": {"sage": version, "admcycles": "1.4",
                        "python": platform.python_version(), "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name:
            hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (admcycles, stable_graph, tautological_ring)},
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "cache_ephemeral": True, "online_lookup": False, "cases": cases,
        "symmetric_graph_check": {"genus": 2, "initial_markings": 0,
                                  "coincident_placements": 2, "resulting_raw_coefficient": [2, 1]},
        "decorated_countercheck": {"class": "psi_2 on Mbar(1,2)",
                                   "extra_marking": 3, "rational_tail_coefficient": [-1, 1]},
        "scope": "Independent incidence construction agrees with admcycles in raw coordinates "
                 "for one and two additional markings. No relation quotient or zero oracle used.",
        "remaining": "Lean graph construction and geometric forgetful compatibility; this "
                     "diagnostic is not a proof of Getzler vanishing or numerical GW reconstruction.",
    }


def main():
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-getzler-forgetful-") as temporary:
        for variable, name in (("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                               ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")):
            location = Path(temporary) / name
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        print(json.dumps(explore(), indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"Getzler forgetful exploration failed: {error}", file=sys.stderr)
        sys.exit(1)
