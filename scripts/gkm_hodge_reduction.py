#!/usr/bin/env python3
"""Explore genus-two surface localization with string and dilaton reduction of vertex integrals."""
import argparse
from functools import cache
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import sys
import tempfile
from unittest.mock import patch

from check_gkm_inputs import RationalFunction, polynomial, unique_object
from export_gkm_inputs import ADMCYCLES_VERSION, SAGE_VERSION, producer_source, require
from gkm_research_query import frame, incoming_claim
from gkm_three_point_descendants import explore, read_report
from gw_query import validate


SEEDS = (((0, 0), (4,)), ((0, 0), (2, 3)), ((0, 0), (2, 2, 2)),
         ((0, 1), (3,)), ((0, 1), (2, 2)), ((0, 2), (2,)),
         ((1, 1), (2,)), ((1, 2), ()))
KIND = "axiomatic_gw.exploration.genus_two_vertex_string_dilaton.v1"


def reduction(seeds):
    """Take ordered psi data and both Hodge indices to the eight native seed integrals."""
    @cache
    def value(lambdas, powers):
        if sum(lambdas) + sum(powers) != 3 + len(powers):
            return 0
        if powers and powers[0] == 0:
            rest = powers[1:]
            return sum(value(lambdas, tuple(sorted(rest[:i] + (k - 1,) + rest[i + 1:])))
                       for i, k in enumerate(rest) if k > 0)
        if powers and powers[0] == 1:
            return (1 + len(powers)) * value(lambdas, powers[1:])
        return seeds[lambdas, powers]

    return lambda lambdas, psis: value(tuple(sorted(lambdas)), tuple(sorted(psis)))


def run(producer, pin, query=None):
    from sage.all import QQ
    from sage.version import version as sage_version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default
    require(sage_version == SAGE_VERSION and version("admcycles") == ADMCYCLES_VERSION,
            "Changed Sage or admcycles version")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    from gkm_localization import stable_map
    require(Path(stable_map.__file__).resolve() == producer / "gkm_localization/stable_map.py",
            "Imported a different stable-map producer")
    direct = stable_map.hodge_integral
    seeds = {(ls, psis): QQ(direct(2, list(ls), list(psis))) for ls, psis in SEEDS}
    value = reduction(seeds)

    # Repeated survivors must appear separately in the string sum. The empty tail
    # in the last dilaton control is stable in genus two.
    controls = [((0, 0), (0, 3, 3)), ((0, 0), (1, 4)), ((1, 0), (0, 4)),
                ((2, 1), (1,)), ((0, 2), (0, 1, 3)), ((0, 1), (2, 1, 2))]
    for ls, psis in controls:
        require(value(ls, psis) == direct(2, list(ls), list(psis)),
                f"String/dilaton disagrees with direct integration at {ls}, {psis}")
    def entry(ls, psis, v):
        v = QQ(v)
        return {"lambda": list(map(int, ls)), "psi": list(map(int, psis)),
                "value": [int(v.numerator()), int(v.denominator())]}

    ledger = [entry(ls, psis, v) for (ls, psis), v in seeds.items()]
    result = {"kind": KIND, "source": pin, "environment": {"sage": sage_version,
              "admcycles": version("admcycles")}, "seeds": ledger,
              "direct_controls": [{"lambda": list(ls), "psi": list(psis)} for ls, psis in controls]}
    if query is None:
        return result
    signatures = set()

    def vertex_integral(g, lambdas, psis, n=None, method="stupid"):
        if g != 2 or len(lambdas) != 2 or n is not None or method != "stupid":
            return direct(g, lambdas, psis, n=n, method=method)
        require(all(0 <= i <= 2 for i in lambdas) and all(p >= 0 for p in psis),
                "Malformed surface Hodge signature")
        signatures.add((tuple(sorted(lambdas)), tuple(sorted(psis))))
        return value(lambdas, psis)

    requests = frame(query)
    with patch.object(stable_map, "hodge_integral", vertex_integral):
        report = explore(producer, pin, requests=requests, genus=2, kind=KIND)
    read_report(json.dumps(report), requests=requests, genus=2, kind=KIND)
    result.update(query=query, vertices=[entry(ls, psis, value(ls, psis))
                                         for ls, psis in sorted(signatures)], localization=report)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    parser.add_argument("--query", type=Path, help="Optional single genus-two research request")
    parser.add_argument("--reference", type=Path, help="Compare the full fraction with a held native report")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    producer, pin = producer_source(args.producer)
    query = None
    if args.reference and not args.query:
        parser.error("--reference requires --query")
    if args.query:
        query, _, _ = validate(json.loads(args.query.read_text(), object_pairs_hook=unique_object))
        require(query["genus"] == 2, "This exploration takes a genus-two request")
    with tempfile.TemporaryDirectory(prefix="gw-vertex-hodge-") as directory:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            path = Path(directory) / variable
            path.mkdir()
            os.environ[variable] = str(path)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        result = run(producer, pin, query)
    if args.reference:
        raw = args.reference.read_bytes()
        original = incoming_claim(query, raw)
        computed, = result["localization"]["cases"]

        def full_field(row):
            frac = row["equivariant"]
            return RationalFunction(polynomial(frac["numerator"]), polynomial(frac["denominator"]))

        require(computed["ordinary"] == original["ordinary"] and full_field(computed) == full_field(original),
                "Reduced exploration and reference localization disagree")
        result["comparison"] = {"native_report_sha256": hashlib.sha256(raw).hexdigest(),
                                "native_kind": original["kind"]}
    encoded = json.dumps(result, sort_keys=True, indent=2) + "\n"
    with args.output.open("x") as output:
        output.write(encoded)


if __name__ == "__main__":
    main()
