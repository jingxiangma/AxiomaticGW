#!/usr/bin/env python3
"""Native three-point localization and claim-bound offline Lean replay.

The numerical exploration uses no copy of the descendant reduction. Replay
compares the actual incoming value with the independently proved Lean engine.
This does not certify localization geometry or import class-valued CohFT data.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import check_gkm_inputs as codec
from export_admcycles_certificate import rational, rational_text, vector
from export_gkm_inputs import producer_source, target_specifications

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "environments/gkm-inputs-osx-arm64.json"
TARGETS = [("X0", "Plane", "plane"), ("X1", "OneBlowup", "hirzebruchOne"),
           ("X2", "TwoBlowups", "blowupTwo")]
REQUESTS = {
    "X0": [((0,), (0,0,0), ("H","H","unit")),
           ((0,), (1,0,0), ("H","unit","unit")),
           ((1,), (1,0,0), ("pt","H","H")),
           ((1,), (2,0,0), ("pt","H","unit")),
           ((1,), (3,0,0), ("pt","unit","unit")),
           ((1,), (3,0,0), ("H","H","unit")),
           ((1,), (0,0,1), ("H","H","pt")),
           ((2,), (2,2,0), ("pt","pt","unit")),
           ((2,), (2,0,2), ("pt","unit","pt")),
           ((2,), (1,1,2), ("pt","pt","unit"))],
    "X1": [((0,0), (0,0,0), ("E1","E1","unit")),
           ((0,0), (1,0,0), ("E1","unit","unit")),
           ((1,0), (1,0,0), ("E1","E1","unit")),
           ((1,0), (2,0,0), ("unit","E1","unit")),
           ((2,0), (1,1,0), ("E1","E1","unit")),
           ((0,1), (1,0,0), ("pt","E1","unit")),
           ((1,1), (1,0,0), ("pt","H","H"))],
    "X2": [((0,0,0), (0,0,0), ("E1","E2","unit")),
           ((1,0,0), (1,0,0), ("E1","E1","unit")),
           ((0,1,0), (1,0,0), ("E1","E1","unit")),
           ((0,1,0), (1,0,0), ("E2","E2","unit")),
           ((1,0,0), (2,0,0), ("unit","E1","unit")),
           ((2,0,0), (1,1,0), ("E1","E1","unit")),
           ((1,1,0), (1,1,0), ("E1","E2","unit")),
           ((0,0,1), (1,0,0), ("H","E1","unit")),
           ((0,1,1), (1,0,0), ("pt","E2","unit")),
           ((1,0,1), (1,0,0), ("pt","E1","unit"))],
}


def explore(producer, pin, *, requests=REQUESTS, genus=0,
            kind="gkm_localization.three_point_descendants"):
    from sage.all import Fan, LaurentPolynomialRing, PolynomialRing, QQ, ZZ
    from sage.version import version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default
    codec.require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
                  "Changed environment")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapsGKM, toric_target_from_fan
    codec.require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
                  "Imported a different producer")
    frames = {f["target"]: f for f in json.loads(INPUT.read_text())["targets"]}
    P = PolynomialRing(QQ, names=("x", "y"))
    K = P.fraction_field()
    R = LaurentPolynomialRing(ZZ, names=("x", "y"))

    def pair(q):
        q = QQ(q)
        return [int(q.numerator()), int(q.denominator())]

    def decode(q):
        def poly(terms):
            return sum(QQ(n)/QQ(d) * P.gen(0)**i * P.gen(1)**j for (i,j), (n,d) in terms)
        return K(poly(q["numerator"])) / K(poly(q["denominator"]))

    def encode(q):
        def poly(p):
            return [[list(map(int, powers)), pair(c)] for powers, c in sorted(p.dict().items())]
        return {"numerator": poly(q.numerator()), "denominator": poly(q.denominator())}

    cases = []
    for spec in target_specifications():
        frame = frames[spec["id"]]
        target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), R,
                                      curve_basis=spec["curves"], name=frame["target"])
        points = [tuple(p) for p in frame["points"]]
        codec.require(points == sorted(target.fixed_points()), "Changed fixed-point indexing")
        basis = {name: target.cohomology_class({p: R(decode(frame["basis_to_fixedpoint"][j][i]))
                                               for j, p in enumerate(points)})
                 for i, name in enumerate(frame["basis"])}
        maps = StableMapsGKM(target)
        for beta, powers, labels in requests[frame["target"]]:
            codec.require(len(powers) == len(labels), "Mismatched insertion data")
            print(f"Localizing {frame['target']} {beta} {list(zip(powers, labels))}", flush=True)
            value = K(maps.integrate(genus, len(powers), (ZZ ** len(beta))(beta),
                                    [(p, basis[a]) for p, a in zip(powers, labels)]))
            codec.require(value.denominator()(0, 0) != 0, "Unresolved ordinary pole")
            ordinary = QQ(value.numerator()(0, 0) / value.denominator()(0, 0))
            cases.append({"target": frame["target"], "genus": genus, "class": list(beta),
                          "powers": list(powers), "labels": list(labels),
                          "equivariant": encode(value), "ordinary": pair(ordinary)})
    return {"schema_version": 1, "kind": kind,
            "source": pin, "input_sha256": hashlib.sha256(INPUT.read_bytes()).hexdigest(),
            "environment": {"sage": version, "admcycles": "1.4"},
            "online_lookup": False, "cache_ephemeral": True, "cases": cases}


def read_report(raw, *, requests=REQUESTS, genus=0,
                kind="gkm_localization.three_point_descendants"):
    report = json.loads(raw, object_pairs_hook=codec.unique_object)
    source = json.loads(INPUT.read_text())
    codec.require(codec.integer(report["schema_version"]) == 1 and
                  report["kind"] == kind, "Wrong schema")
    codec.require(report["input_sha256"] == hashlib.sha256(INPUT.read_bytes()).hexdigest() and
                  report["source"] == source["source"], "Changed source provenance")
    codec.require(report["environment"] == {"sage": "10.9", "admcycles": "1.4"} and
                  report["online_lookup"] is False and report["cache_ephemeral"] is True,
                  "Changed environment or cache policy")
    grouped = {t: [] for t, _, _ in TARGETS}
    for case in report["cases"]:
        codec.require(case["target"] in grouped and codec.integer(case["genus"]) == genus,
                      "Wrong target/genus")
        request = (tuple(map(codec.integer, case["class"])),
                   tuple(map(codec.integer, case["powers"])), tuple(case["labels"]))
        codec.require(request in requests[case["target"]], "Changed request")
        q = case["equivariant"]
        codec.require(set(q) == {"numerator", "denominator"}, "Wrong fraction fields")
        function = codec.RationalFunction(codec.polynomial(q["numerator"]), codec.polynomial(q["denominator"]))
        rational(case["ordinary"])
        codec.require(function.ordinary() == codec.rational(case["ordinary"]), "Incorrect specialization")
        grouped[case["target"]].append(case)
    for target, cases in grouped.items():
        received = [(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])) for c in cases]
        codec.require(len(received) == len(set(received)) and set(received) == set(requests[target]),
                      "Incomplete or duplicate request coverage")
    return report, grouped


def emit(raw):
    _, grouped = read_report(raw)
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: JMA", "-/", "module", "",
             "public import AxiomaticGW.Surfaces.Fixtures.ThreePointDescendants", "",
             "/-!", "# Native three-point descendant replay", "",
             "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
             "Each actual incoming value is compared with the proved descendant evaluator.",
             "The digest is provenance, not a proof of localization geometry.", "-/", "",
             "@[expose] public section", "", "namespace AxiomaticGW.GKM.ThreePointDescendantReplay", ""]
    label = {"unit": ".unit", "H": ".hyperplane", "E1": ".exceptional 0", "E2": ".exceptional 1", "pt": ".point"}
    for target, namespace, surface in TARGETS:
        cases = grouped[target]
        requests = ["(" + vector(list(map(str, c["class"]))) + ", " +
                    vector(list(map(str, c["powers"]))) + ", " +
                    vector([label[x] for x in c["labels"]]) + ")" for c in cases]
        lines += [f"namespace {namespace}", "",
                  f"def requests : Fin {len(cases)} → SurfaceThreePointDescendants.Request .{surface} :=",
                  "  ![" + ",\n    ".join(requests) + "]", "",
                  f"def values : Fin {len(cases)} → ℚ :=",
                  "  " + vector([rational_text(rational(c["ordinary"])) for c in cases]), "",
                  "/-- Coverage is checked against the separately held requests. -/",
                  "theorem coverage : Finset.univ.image requests =",
                  f"    (SurfaceThreePointDescendants.requests .{surface}).toFinset := by decide +kernel", "",
                  "/-- The value, full curve, both insertion data and their order are claim-bound. -/",
                  "theorem accepted : ∀ i, values i = SurfaceDescendant.threePointValue",
                  f"    .{surface} (requests i).1 (requests i).2.1 (requests i).2.2 := by decide +kernel", "",
                  f"end {namespace}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GKM.ThreePointDescendantReplay", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    native = commands.add_parser("explore")
    native.add_argument("--producer", required=True, type=Path)
    native.add_argument("--output", required=True, type=Path)
    replay = commands.add_parser("replay")
    replay.add_argument("report", type=Path)
    replay.add_argument("--output", required=True, type=Path)
    replay.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.command == "explore":
        producer, pin = producer_source(args.producer)
        with tempfile.TemporaryDirectory(prefix="gw-threepoint-native-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = explore(producer, pin)
        args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    else:
        result = emit(args.report.read_bytes())
        if args.check:
            codec.require(args.output.read_text() == result, "Saved replay differs from generated source")
        else:
            args.output.write_text(result)


if __name__ == "__main__":
    main()
