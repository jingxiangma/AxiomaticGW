#!/usr/bin/env python3
"""Diagnose the component-dimension and cancellation boundary in the initial L24 row.

Input is the previously checked native decorated-pullback payload. This exact
Python comparison is exploration evidence, not a Lean proof of class equality.
The payload's CotangentTerm syntax has only psi decorations, so its graph JSON
omits kappa fields; zero kappa arrays are added solely for the held frame key.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from export_admcycles_certificate import require
from export_l24_corrections import FRAME_IDS
from test_l24_normalization import accumulate, flags, key, power, relabel, sparse

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(payload_path):
    old_path = ROOT / "environments/decorated-forgetful-exploration.json"
    bp_path = ROOT / "environments/belorousski-pandharipande.json"
    report_path = ROOT / "environments/l24-normalization-exploration.json"
    old = json.loads(old_path.read_bytes())
    require(digest(payload_path) == old["lean_payload_sha256"],
            "Native payload differs from the previously validated source")
    payload = json.loads(payload_path.read_bytes())
    bp = json.loads(bp_path.read_bytes())
    report = json.loads(report_path.read_bytes())
    graph_index = {key(g): i for i, g in enumerate(report["graphs"])}
    frame = set(FRAME_IDS)
    rows, before_average, extras = {}, set(), set()
    terms, pruned, expanded, seen = 0, 0, 0, set()
    for case in payload["cases"]:
        if case["additional_markings"] != 1 or not case["name"].startswith("bp_"):
            continue
        _, i, e = case["name"].split("_")
        i, e = int(i), int(e)
        require((i, e) not in seen, "Repeated BP marking assignment")
        seen.add((i, e))
        paper = bp["published_terms"][i]
        coefficient = Fraction(*paper["coefficient"]) / paper["automorphism"]
        for term in case["terms"]:
            terms += 1
            raw = dict(term["graph"])
            raw.pop("codimension")
            raw["kappa"] = [[0] * 3 for _ in raw["genus"]]
            raw = relabel(raw, [3, 0, 1, 2])
            for label, weight in enumerate([-1, 3, 1, 1]):
                graph = dict(raw, leg_psi=raw["leg_psi"][:])
                graph["leg_psi"][label] += 1
                if any(sum(power(graph, f) for f in flags(graph, v)) >
                       3 * genus - 3 + len(flags(graph, v))
                       for v, genus in enumerate(graph["genus"])):
                    pruned += 1
                    continue
                before_average.add(graph_index[key(graph)])
                for permutation in report["permutations"]:
                    index = graph_index[key(relabel(graph, permutation))]
                    expanded += 1
                    if index not in frame:
                        extras.add(index)
                    accumulate(rows, index, coefficient * term["coefficient"] * weight / 72)
    require(seen == {(i, e) for i in range(20) for e in range(6)},
            "Missing original BP diagrams or marking assignments")
    require(rows == sparse(report["initial"]),
            "Dimension-pruned averaged native BP sum differs from the initial claim")
    return {
        "schema_version": 1,
        "status": "exact Python diagnostic; initial Lean class replay remains pending",
        "source_sha256": {"native_payload": digest(payload_path),
                          "prior_comparison": digest(old_path),
                          "bp_report": digest(bp_path), "l24_report": digest(report_path)},
        "bp_marking_assignments": len(seen),
        "signed_pullback_terms": terms,
        "weighted_terms_before_pruning": 4 * terms,
        "component_dimension_zero_terms": pruned,
        "retained_summands_after_sixfold_average": expanded,
        "extra_columns_before_average": sorted(before_average - frame),
        "extra_columns_after_average_before_cancellation": sorted(extras),
        "initial_nonzero_terms": len(rows),
        "initial_claim_matches_after_pruning_and_cancellation": True,
        "remaining_proof": "Connect actual BP terms to checked graph destinations, apply "
                           "component dimension vanishing, and certify all auxiliary cancellations.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_payload", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = json.dumps(audit(args.native_payload), indent=2, sort_keys=True) + "\n"
    if args.check:
        require(args.output.read_text() == text, "Stored diagnostic differs")
    else:
        args.output.write_text(text)


if __name__ == "__main__":
    main()
