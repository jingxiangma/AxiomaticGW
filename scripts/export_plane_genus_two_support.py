#!/usr/bin/env python3
"""Certify the lower-genus support needed by the shifted plane quartic equations.

The genus-two benchmark remains energy twelve. Its source-degree-five BP
equations need primary lower-genus values through energy fifteen. Reuse the
existing candidate recurrences and original finite-table kernel checkers.
"""

import argparse
import hashlib
import json

import export_surface_genus_zero_tables as rational
import export_surface_genus_one_tables as elliptic

ROOT = rational.ROOT
BOUND = 15
MANIFEST = ROOT / "environments/plane-genus-two-lower-genus-support.json"


def outputs():
    cases = []
    for genus, table in [(0, rational.table), (1, elliptic.table)]:
        rows = []
        for curve, value in table("P2", BOUND).items():
            energy = rational.energy("P2", curve)
            rows.append({"curve": list(curve), "energy": energy,
                         "point_count": max(energy + genus - 1, 0),
                         "domain": "geometric" if energy else "auxiliary_zero_class_empty_query",
                         "value": [value.numerator, value.denominator]})
        cases.append({"target": "P2", "genus": genus, "energy_bound": BOUND, "rows": rows})
    report = {
        "schema_version": 1,
        "scope": "Lower-genus primary support for the unchanged genus-two plane quartic benchmark",
        "source": [
            {"manifest": str(p.relative_to(ROOT)),
             "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}
            for p in [rational.MANIFEST, elliptic.MANIFEST]],
        "comparison_limits": [
            "Candidate recurrences reuse the existing WDVV/Getzler sources and initial data.",
            "All six classes in each genus, including zero, require original kernel checks.",
            "Energy fifteen is internal support, not a change to the fixed release benchmarks.",
            "These tables do not certify any genus-two value or add a geometric seed."],
        "cases": cases}
    raw = json.dumps(report, indent=2) + "\n"
    digest = hashlib.sha256(raw.encode()).hexdigest()
    zero, one = "PlaneGenusZeroSupport", "PlaneGenusOneSupport"
    directory = ROOT / "AxiomaticGW/Surfaces/Fixtures"
    return {
        MANIFEST: raw,
        directory / f"{zero}.lean": rational.lean_module(cases[0], digest, namespace=zero),
        directory / f"{one}.lean": elliptic.lean_module(
            cases[1], digest, namespace=one, rational_module=zero)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for path, content in outputs().items():
        if args.check:
            if path.read_text() != content:
                raise SystemExit(f"Changed generated support: {path.relative_to(ROOT)}")
        else:
            path.write_text(content)
        print(("checked " if args.check else "wrote ") + str(path.relative_to(ROOT)))


if __name__ == "__main__":
    main()
