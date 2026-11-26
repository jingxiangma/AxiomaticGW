#!/usr/bin/env python3
"""Exact GKM comparison for the complete plane genus-two few-marking suite.

The held requests are determined by the fixed benchmark bounds and the virtual
surface dimension. The native producer supplies candidate values only. This
report does not import CohFT classes or certify equivariant localization.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from export_gkm_inputs import producer_source
from export_admcycles_certificate import rational_text
from gkm_three_point_descendants import explore as native_explore, read_report as parse_report
from genus_two_few_marking_requests import requests_for
import check_gkm_inputs as codec

ROOT = Path(__file__).resolve().parents[1]
KIND = "gkm_localization.plane_genus_two_few_markings"
MANIFEST = ROOT / "environments/genus-two-plane-few-markings-requests.json"


def benchmark_requests():
    # The existing plane replay remains the unchanged X0 subset of the full contract.
    return {"X0": requests_for("X0"), "X1": [], "X2": []}


REQUESTS = benchmark_requests()

# Separate expensive proofs by marking sector. Every held index occurs once.
COMPUTATION_GROUPS = (("OnePoint", 0, 3), ("Unit", 3, 21),
                      ("Hyperplane", 21, 36), ("Point", 36, 48))


def request_manifest():
    return {"schema_version": 1, "kind": "axiomatic_gw.plane_genus_two_few_markings.requests",
            "genus": 2, "positive_energy_bound": 4, "maximum_markings": 2,
            "dimension_equation": "sum(psi + complex_codimension) = 3*degree + genus - 1 + n",
            "ordered_markings": True, "request_count": len(REQUESTS["X0"]),
            "counts_by_arity": {str(n): sum(len(p) == n for _, p, _ in REQUESTS["X0"])
                                for n in range(3)},
            "requests": [{"target": "X0", "genus": 2, "class": list(b),
                          "powers": list(p), "labels": list(a)} for b, p, a in REQUESTS["X0"]],
            "reference_method": "Pinned native GKM localization, computed before Lean value certification",
            "independence_limit": "Separate numerical implementation; shared admcycles and tautological/Hodge mathematics"}


def read_report(raw):
    codec.require(json.loads(MANIFEST.read_bytes()) == request_manifest(), "Changed held query manifest")
    return parse_report(raw, requests=REQUESTS, genus=2, kind=KIND)


def compare_candidates(lean_raw, gkm_raw):
    """Compare complete exact outputs without claiming mathematical certification."""
    _, grouped = read_report(gkm_raw)
    reference = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])):
                 codec.rational(c["ordinary"]) for c in grouped["X0"]}
    report = json.loads(lean_raw, object_pairs_hook=codec.unique_object)
    codec.require(set(report) == {"schema_version", "kind", "positive_energy_bound",
                                  "maximum_markings", "cases"}, "Wrong candidate fields")
    codec.require(codec.integer(report["schema_version"]) == 1 and
                  report["kind"] == "axiomatic_gw.plane_genus_two_few_markings" and
                  codec.integer(report["positive_energy_bound"]) == 4 and
                  codec.integer(report["maximum_markings"]) == 2, "Wrong candidate scope")
    seen = set()
    for case in report["cases"]:
        codec.require(set(case) == {"target", "genus", "class", "powers", "labels", "ordinary"},
                      "Wrong candidate query fields")
        codec.require(case["target"] == "X0" and codec.integer(case["genus"]) == 2,
                      "Wrong candidate target/genus")
        key = (tuple(map(codec.integer, case["class"])),
               tuple(map(codec.integer, case["powers"])), tuple(case["labels"]))
        codec.require(key in reference and key not in seen, "Changed or duplicate candidate request")
        codec.require(codec.rational(case["ordinary"]) == reference[key], "Candidate value disagrees")
        seen.add(key)
    codec.require(seen == set(reference), "Incomplete candidate coverage")
    return len(seen)


def requests_source():
    """Freeze ordered requests, independently of every numerical answer."""
    names = {"unit": ".unit", "H": ".hyperplane", "pt": ".point"}
    queries = []
    for beta, powers, labels in REQUESTS["X0"]:
        states = ", ".join(f"⟨{names[a]}, {k}⟩" for a, k in zip(labels, powers))
        queries.append(f"⟨2, ![{beta[0]}], [{states}]⟩")
    return "\n".join([
        "/-", "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: JMA", "-/", "module", "",
        "public import AxiomaticGW.Surfaces.PlaneGenusTwoFewMarkings", "",
        "/-!", "# Held ordered plane genus-two few-marking requests", "",
        "Manifest SHA256: " + hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
        "The requests depend only on the fixed bounds and dimension equation.",
        "Coverage is checked against the separately proved complete mathematical frame.",
        "No numerical values occur in this artifact.", "-/", "",
        "@[expose] public section", "set_option Elab.async false",
        "set_option maxRecDepth 20000", "",
        "namespace AxiomaticGW.GenusTwoPlaneFewMarkingRequests", "",
        "open BelorousskiPandharipande", "",
        "/-- The held 48 ordered queries, retaining every state and descendant power. -/",
        "def requests (i : Fin 48) : SurfaceQuery .plane :=",
        "  (#[" + ",\n    ".join(queries) + "] : Array (SurfaceQuery .plane))[i.val]", "",
        "/-- Every required ordered request occurs; no extra request is included. -/",
        "theorem coverage : Finset.univ.image requests = planeFewMarkingQueries := by",
        "  decide +kernel", "",
        "/-- The explicit request list has no repeated complete query. -/",
        "theorem requests_injective : Function.Injective requests := by",
        "  decide +kernel", "",
        "end AxiomaticGW.GenusTwoPlaneFewMarkingRequests", ""])


def emit(raw, *, cached=False):
    """Generate kernel proofs for the actual incoming values and complete queries."""
    _, grouped = read_report(raw)
    indexed = {(tuple(c["class"]), tuple(c["powers"]), tuple(c["labels"])): c
               for c in grouped["X0"]}
    cases = [indexed[q] for q in REQUESTS["X0"]]
    names = {"unit": ".unit", "H": ".hyperplane", "pt": ".point"}
    queries = []
    for c in cases:
        states = ", ".join(f"⟨{names[a]}, {k}⟩" for a, k in zip(c["labels"], c["powers"]))
        queries.append(f"⟨{c['genus']}, ![{c['class'][0]}], [{states}]⟩")
    values = ", ".join(rational_text(codec.rational(c["ordinary"])) for c in cases)
    imports = (["public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsReplay"]
               if cached else [
                   "public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneFewMarkingRequests",
                   "public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine",
                   "public import AxiomaticGW.Surfaces.PlaneGenusTwoQueryCertificate"])
    namespace = "PlaneGenusTwoFewMarkingsClaim" if cached else "PlaneGenusTwoFewMarkingsReplay"
    lines = [
        "/-", "Copyright (c) 2026 JMA. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: JMA", "-/", "module", "",
        *imports, "",
        "/-!", "# Complete native plane genus-two few-marking replay", "",
        "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
        "Each ordinary value is checked against its complete descendant query.",
        "The degree-one canonical table and lower-genus caches are already proved.",
        "This does not certify equivariant localization or import CohFT classes.", "-/", "",
        "@[expose] public section", "set_option Elab.async false",
        "set_option maxRecDepth 65536", "set_option maxHeartbeats 4000000",
        "set_option cbv.maxSteps 4000000", "",
        "namespace AxiomaticGW.GKM." + namespace, "",
        "open BelorousskiPandharipande", "",
        "/-- Complete ordered incoming requests, checked against the independent benchmark frame. -/",
        "def requests (i : Fin 48) : SurfaceQuery .plane :=",
        "  (#[" + ",\n    ".join(queries) + "] : Array (SurfaceQuery .plane))[i.val]", "",
        "/-- Exact incoming ordinary values; subsequent replay certifies each full claim. -/",
        "def values (i : Fin 48) : ℚ :=",
        "  (#[" + values + "] : Array ℚ)[i.val]", "",
        "/-- Every incoming request matches the independently held full query. -/",
        "theorem coverage : ∀ i, requests i = GenusTwoPlaneFewMarkingRequests.requests i := by",
        "  decide +kernel", "",
    ]
    if cached:
        # Both inputs are checked: a cached proof is reusable only for that exact claim.
        lines += [
            "/-- Bind every complete incoming query and value to its checked computation. -/",
            "theorem checked : ∀ i, requests i = PlaneGenusTwoFewMarkingsReplay.requests i ∧",
            "    values i = PlaneGenusTwoFewMarkingsReplay.values i := by",
            "  decide +kernel", "",
            "/-- Reuse the existing proof only after checking the complete incoming claim. -/",
            "theorem accepted (i : Fin 48) : planeQueryValue? (requests i) = some (values i) := by",
            "  rw [(checked i).1, (checked i).2]",
            "  exact PlaneGenusTwoFewMarkingsReplay.accepted i", "",
            "end AxiomaticGW.GKM." + namespace, ""]
        return "\n".join(lines)
    lines += [
        "-- Avoid evaluating unused recursive arguments of Fin.cases during cbv.",
        "private theorem vectorLookup {α : Type*} {n : ℕ} (x : α) (xs : Fin n → α)",
        "    (i : Fin (n + 1)) : Matrix.vecCons x xs i =",
        "      if h : i.val = 0 then x else xs ⟨i.val - 1, by omega⟩ := by",
        "  rcases i with ⟨i, hi⟩", "  cases i <;> rfl", "",
        "private theorem rationalCached (beta : SurfaceTarget.plane.Curve) :",
        "    SurfaceGenusZero.pointValue .plane beta =",
        "      if SurfaceTarget.plane.effective.energy beta ≤ 15",
        "      then PlaneGenusZeroSupport.values beta else SurfaceGenusZero.pointValue .plane beta := by",
        "  split_ifs with h", "  · exact (PlaneGenusZeroSupport.values_eq beta h).symm", "  · rfl", "",
        "private theorem ellipticCached (beta : SurfaceTarget.plane.Curve) :",
        "    SurfaceGenusOne.pointValue .plane beta =",
        "      if SurfaceTarget.plane.effective.energy beta ≤ 15",
        "      then PlaneGenusOneSupport.values beta else SurfaceGenusOne.pointValue .plane beta := by",
        "  split_ifs with h", "  · exact (PlaneGenusOneSupport.values_eq beta h).symm", "  · rfl", "",
        "attribute [local cbv_eval] vectorLookup rationalCached ellipticCached", "",
    ]
    for index in range(48):
        lines += [f"private theorem value_{index} : planeQueryValueWith? GenusTwoPlaneLine.values",
                  f"    (requests {index}) = some (values {index}) := by cbv", ""]
    lines += ["/-- Complete evaluation of every held request, with no added numerical seed. -/",
              "theorem computed (i : Fin 48) : planeQueryValueWith? GenusTwoPlaneLine.values",
              "    (requests i) = some (values i) := by", "  fin_cases i"]
    lines += [f"  · exact value_{index}" for index in range(48)]
    lines += ["", "/-- Every original descendant value follows from the accepted canonical table. -/",
              "theorem accepted (i : Fin 48) : planeQueryValue? (requests i) = some (values i) := by",
              "  rw [← planeQueryValueWith?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted",
              "    (requests i) (by revert i; decide +kernel)]", "  exact computed i", "",
              "end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay", ""]
    return "\n".join(lines)


def split_sources(raw):
    """Keep numerical proofs reusable independently of canonical-table acceptance.

    The arithmetic modules use a literal canonical table. The two-marked
    sectors reuse complete checked ancestor equations and descendant expansions.
    The final assembly identifies the canonical table with the accepted line
    table before applying soundness. Incoming GKM values are never new seeds.
    """
    source = emit(raw)
    prefix = "PlaneGenusTwoFewMarkings"
    namespace = "AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsReplay"
    data, calculations = source.split("-- Avoid evaluating unused recursive arguments", 1)
    helpers = "-- Avoid evaluating unused recursive arguments" + calculations.split(
        "attribute [local cbv_eval]", 1)[0]
    helpers = helpers.replace("private theorem ", "theorem ")
    data = data.replace("set_option maxHeartbeats 4000000\n", "")
    for line in data.splitlines():
        if line.startswith("  (#[") and line.endswith("] : Array ℚ)[i.val]"):
            entries = line[len("  (#["):-len("] : Array ℚ)[i.val]")].split(", ")
            wrapped = "  (#[" + ",\n    ".join(", ".join(entries[i:i + 4])
                                                for i in range(0, len(entries), 4))
            data = data.replace(line, wrapped + "] : Array ℚ)[i.val]")
    data = data.replace(
        "public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine",
        "public import AxiomaticGW.Surfaces.Fixtures.PlaneGenusOneSupport")
    data = data.replace("# Complete native plane genus-two few-marking replay",
                        "# Incoming plane few-marking claims and arithmetic support")
    data = data.replace(
        "The degree-one canonical table and lower-genus caches are already proved.",
        "The literal canonical table is candidate data here. Final replay identifies it\n"
        "with the existing accepted line table. Lower-genus caches have separate proofs.")
    data += (
        "/-- Literal canonical candidates; their acceptance is checked in the final assembly. -/\n"
        "def canonicalValues (d : ℕ) : Fin 3 → ℚ :=\n"
        "  match d with\n"
        "  | 0 => ![0, -1 / 960, 0]\n"
        "  | _ => ![0, 0, 0]\n\n" + helpers + "end " + namespace + "\n")
    result = {prefix + "Data.lean": data}

    def header(imports, title, description):
        return "\n".join([
            "/-", "Copyright (c) 2026 JMA. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            "Authors: JMA", "-/", "module", "", *imports, "",
            "/-!", "# " + title, "", description, "-/", "",
            "@[expose] public section", "set_option Elab.async false",
            "set_option maxRecDepth 65536",
            "set_option cbv.maxSteps 4000000", ""])

    for name, start, stop in COMPUTATION_GROUPS:
        count = stop - start
        cached = start != 0
        imports = ["public import AxiomaticGW.GKM.Fixtures." + prefix + "Data"]
        description = (
            "Every displayed query is evaluated against the literal canonical candidate table.\n"
            "Final acceptance separately identifies that table with the certified line table.")
        if cached:
            imports += ["public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsReplay",
                        "public import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoAncestorsDescendants"]
            description = (
                "Each full query follows from separately checked ancestor equations and its\n"
                "complete descendant expansion. The original canonical table is unchanged.")
        lines = [header(
            imports, "Plane few-marking arithmetic: " + name, description),
            "namespace " + namespace + "." + name, "",
            "open BelorousskiPandharipande", ""]
        if not cached:
            lines += ["attribute [local cbv_eval] vectorLookup rationalCached ellipticCached", ""]
        for index in range(start, stop):
            if not cached:
                lines += ["set_option maxHeartbeats 4000000 in",
                          "-- Kernel proof of this complete finite descendant calculation."]
            lines += [f"private theorem value_{index} : planeQueryValueWith? canonicalValues",
                      f"    (requests {index}) = some (values {index}) := by" +
                      ("" if cached else " cbv")]
            if cached:
                lines += [f"  change planeQueryValueWith? GenusTwoPlaneLine.values (requests {index}) = _",
                          "  rw [← PlaneGenusTwoAncestors.query_eq]",
                          f"  exact PlaneGenusTwoAncestors.cached_computation {index}"]
            lines += [""]
        lines += ["/-- Every request in this sector is checked, including its full ordered insertions. -/",
                  f"theorem computed (i : Fin {count}) : planeQueryValueWith? canonicalValues",
                  f"    (requests ⟨{start} + i.val, by omega⟩) =",
                  f"      some (values ⟨{start} + i.val, by omega⟩) := by", "  fin_cases i"]
        lines += [f"  · exact value_{index}" for index in range(start, stop)]
        lines += ["", "end " + namespace + "." + name, ""]
        result[prefix + name + ".lean"] = "\n".join(lines)

    imports = ["public import AxiomaticGW.GKM.Fixtures." + prefix + name
               for name, _, _ in COMPUTATION_GROUPS]
    imports += ["public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine"]
    lines = [header(imports, "Complete native plane genus-two few-marking replay",
                    "The separately checked arithmetic covers all 48 held queries.\n"
                    "The candidate canonical table is identified with the accepted line table\n"
                    "before its soundness theorem certifies the original descendant algorithm.\n"
                    "This does not certify equivariant localization or import CohFT classes."),
             "namespace " + namespace, "", "open BelorousskiPandharipande", "",
             "/-- Candidate arithmetic uses exactly the separately accepted canonical table. -/",
             "theorem canonicalValues_eq : canonicalValues = GenusTwoPlaneLine.values := rfl", "",
             "/-- Complete evaluation of every held request, with no added numerical seed. -/",
             "theorem computed (i : Fin 48) : planeQueryValueWith? GenusTwoPlaneLine.values",
             "    (requests i) = some (values i) := by",
             "  rw [← canonicalValues_eq]", "  fin_cases i"]
    for name, start, stop in COMPUTATION_GROUPS:
        lines += [f"  · exact {name}.computed {index - start}" for index in range(start, stop)]
    lines += ["", "/-- Every original descendant value follows from the accepted canonical table. -/",
              "theorem accepted (i : Fin 48) : planeQueryValue? (requests i) = some (values i) := by",
              "  rw [← planeQueryValueWith?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted",
              "    (requests i) (by revert i; decide +kernel)]", "  exact computed i", "",
              "end " + namespace, ""]
    result[prefix + "Replay.lean"] = "\n".join(lines)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    native = commands.add_parser("explore")
    native.add_argument("--producer", required=True, type=Path)
    native.add_argument("--output", required=True, type=Path)
    check = commands.add_parser("check")
    check.add_argument("report", type=Path)
    frame = commands.add_parser("frame")
    frame.add_argument("--output", required=True, type=Path)
    frame.add_argument("--check", action="store_true")
    comparison = commands.add_parser("compare")
    comparison.add_argument("lean_report", type=Path)
    comparison.add_argument("gkm_report", type=Path)
    replay = commands.add_parser("replay")
    replay.add_argument("report", type=Path)
    replay.add_argument("--output", required=True, type=Path)
    replay.add_argument("--check", action="store_true")
    replay.add_argument("--split-computation", action="store_true",
                        help="Separate reusable arithmetic sectors from final table acceptance")
    binding = commands.add_parser("bind", help="Replay exact claims using the checked 48-value fixture")
    binding.add_argument("report", type=Path)
    binding.add_argument("--output", required=True, type=Path)
    binding.add_argument("--check", action="store_true")
    args = parser.parse_args()
    codec.require(json.loads(MANIFEST.read_bytes()) == request_manifest(), "Changed held query manifest")
    if args.command == "explore":
        producer, pin = producer_source(args.producer)
        with tempfile.TemporaryDirectory(prefix="gw-plane-few-markings-") as directory:
            os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                cache = Path(directory) / name
                cache.mkdir()
                os.environ[name] = str(cache)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            report = native_explore(producer, pin, requests=REQUESTS, genus=2, kind=KIND)
        raw = (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()
        read_report(raw)
        args.output.write_bytes(raw)
    elif args.command == "check":
        read_report(args.report.read_bytes())
    elif args.command == "compare":
        count = compare_candidates(args.lean_report.read_bytes(), args.gkm_report.read_bytes())
        print(f"All {count} exact candidate values agree; this comparison is not kernel certification.")
        return
    elif args.command in {"replay", "bind"}:
        if args.command == "replay" and args.split_computation:
            sources = split_sources(args.report.read_bytes())
            codec.require(args.output.name == "PlaneGenusTwoFewMarkingsReplay.lean",
                          "Split replay requires the canonical assembly filename")
            for name, source in sources.items():
                path = args.output.with_name(name)
                if args.check:
                    codec.require(path.read_text() == source, "Split replay source differs: " + name)
                else:
                    path.write_text(source)
            print("Generated all 48 arithmetic claims; each module still requires Lean checking.")
            return
        source = emit(args.report.read_bytes(), cached=args.command == "bind")
        if args.check:
            codec.require(args.output.read_text() == source, "Replay source differs")
        else:
            args.output.write_text(source)
    else:
        source = requests_source()
        if args.check:
            codec.require(args.output.read_text() == source, "Held request source differs")
        else:
            args.output.write_text(source)
    print("The 48 held requests are fixed; numerical values require separate Lean replay.")


if __name__ == "__main__":
    main()
