#!/usr/bin/env python3
"""Explore exact surface Getzler polynomials from the frozen admcycles frame.

This independent graph evaluator collects component variables by full curve
class and insertion multiset. No GW values or numerical recurrences are
asserted. The elliptic probe keeps one variable, substitutes classical cubic
tails, and sets all other component variables to zero.
"""

import argparse
import gzip
import hashlib
import importlib.metadata
from itertools import product
import json
import os
from pathlib import Path
import platform
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "environments/getzler-candidate-osx-arm64.json"
SOURCE_SHA256 = "ccd8a8f941e9d2d503ec91e29b2be527bf0c91ce111599e6ec56118f6994ecb7"


def compositions(n, slots):
    if slots == 1:
        yield (n,)
    else:
        for first in range(n + 1):
            for tail in compositions(n - first, slots - 1):
                yield (first,) + tail


def curve_assignments(beta, vertices):
    for columns in product(*(tuple(compositions(n, vertices)) for n in beta)):
        yield tuple(tuple(column[v] for column in columns) for v in range(vertices))


def explore(output_directory=None):
    from sage.all import PolynomialRing, QQ
    from sage.version import version

    if version != "10.9" or importlib.metadata.version("admcycles") != "1.4":
        raise RuntimeError("Review the pinned Sage/admcycles environment")
    data = SOURCE.read_bytes()
    if hashlib.sha256(data).hexdigest() != SOURCE_SHA256:
        raise RuntimeError("The original marked Getzler request changed")
    frame = json.loads(data)
    ring = PolynomialRing(QQ, "elliptic")
    unknown = ring.gen()
    cases = []
    # Codes: unit=0, hyperplane=1, point=2, exceptional E_i=3+i.
    for target, blowups, beta, extra in (
        ("P2", 0, (1,), 1),
        ("F1", 1, (1, 1), 1),
        ("Bl2P2", 2, (1, 1, 1), 1),
        ("Bl2P2", 2, (1, 1, 0), 0),
    ):
        basis = tuple(range(3 + blowups))
        dual = (2, 1, 0) + tuple(range(3, 3 + blowups))
        weights = (1, 1, 1) + (-1,) * blowups
        collected = {}
        raw_terms = 0
        for graph, ratio in zip(frame["graphs"], frame["requested"]):
            coefficient = QQ(ratio[0]) / ratio[1]
            vertices = len(graph["genus"])
            classes = tuple(curve_assignments(beta, vertices))
            for placement in product(range(vertices), repeat=extra):
                markings = graph["leg_vertices"] + list(placement)
                for states in product(basis, repeat=len(graph["endpoints"])):
                    insertions = [[] for _ in range(vertices)]
                    for label, vertex in enumerate(markings):
                        insertions[vertex].append((1 if label < 4 else 2, 0))
                    weight = coefficient
                    for state, (left, right) in zip(states, graph["endpoints"]):
                        insertions[left].append((state, 0))
                        insertions[right].append((dual[state], 0))
                        weight *= weights[state]
                    for assignment in classes:
                        monomial = tuple(sorted(
                            (graph["genus"][v], assignment[v], tuple(sorted(insertions[v])))
                            for v in range(vertices)))
                        collected[monomial] = collected.get(monomial, QQ(0)) + weight
                        raw_terms += 1
        collected = {m: c for m, c in collected.items() if c}

        def substitute(key):
            genus, curve, insertions = key
            if genus == 1 and curve == beta and insertions == ((2, 0),) * (extra + 2):
                return unknown
            if genus != 0 or any(curve) or len(insertions) != 3:
                return ring.zero()
            states = tuple(a for a, psi in insertions if psi == 0)
            if len(states) != 3:
                return ring.zero()
            if states in ((0, 0, 2), (0, 1, 1)):
                return ring.one()
            if states[0] == 0 and states[1] == states[2] and states[1] >= 3:
                return -ring.one()
            return ring.zero()

        probe = ring.zero()
        for monomial, coefficient in collected.items():
            term = ring(coefficient)
            for key in monomial:
                term *= substitute(key)
            probe += term
        if probe != -9 * unknown:
            raise RuntimeError(f"Unexpected elliptic coefficient for {target}: {probe}")
        # Serializing ordered data makes the complete sparse polynomial auditable.
        terms = [[monomial, [int(c.numerator()), int(c.denominator())]]
                 for monomial, c in sorted(collected.items())]
        payload = json.dumps(terms, separators=(",", ":")).encode()
        record = {"target": target, "curve": beta, "extra_markings": extra,
                      "raw_terms": raw_terms, "collected_monomials": len(terms),
                      "distinct_component_variables": len({q for m in collected for q in m}),
                      "polynomial_sha256": hashlib.sha256(payload).hexdigest(),
                      "probe": str(probe), "probe_coefficient": [-9, 1]}
        if output_directory is not None:
            output_directory.mkdir(parents=True, exist_ok=True)
            name = f"{target}-{'-'.join(map(str, beta))}-n{extra}.json.gz"
            destination = output_directory / name
            compressed = gzip.compress(payload, mtime=0)
            destination.write_bytes(compressed)
            record["polynomial_file"] = os.path.relpath(destination.resolve(), ROOT)
            record["compressed_sha256"] = hashlib.sha256(compressed).hexdigest()
        cases.append(record)
    return {
        "status": "exploration_passed",
        "environment": {"sage": version, "admcycles": "1.4",
                        "python": platform.python_version(), "architecture": platform.machine()},
        "input": str(SOURCE.relative_to(ROOT)), "input_sha256": SOURCE_SHA256,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "normalization": "raw_gluing_pushforward; original held request; no extra automorphism factor",
        "method": "independent incidence expansion of the frozen admcycles frame in Sage QQ",
        "polynomial_format": "list of [monomial, [numerator, denominator]]; monomial is a sorted "
                             "list of [genus, full_curve, sorted [state_code, psi_power] pairs]; "
                             "state codes are unit=0, H=1, pt=2, E_i=3+i",
        "cases": cases,
        "nonclaims": ["No geometric input is proved by these computations",
                      "The probe is a formal substitution, not a numerical GW solution",
                      "The coefficient has not yet been isolated uniformly in arbitrary marking count",
                      "No numerical benchmark or termination gate is discharged"],
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--polynomials-dir", type=Path,
                        help="save the complete sparse polynomials as reproducible gzip JSON")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="gw-surface-getzler-") as cache:
        os.environ["DOT_SAGE"] = cache
        os.environ["XDG_CACHE_HOME"] = cache
        print(json.dumps(explore(args.polynomials_dir), indent=2, sort_keys=True))
