#!/usr/bin/env python3
"""Freeze all few-marking requests before computing their numerical answers.

The corresponding complete Lean domain is SurfaceGenusTwo.fewMarkingQueries.
This manifest carries no expected values and does not certify a reconstruction.
"""
import argparse
import itertools
import json
from pathlib import Path

TARGETS = {
    "X0": {"coordinates": ["H"], "weights": [3], "labels": ["unit", "H", "pt"]},
    "X1": {"coordinates": ["E1", "F"], "weights": [1, 2],
           "labels": ["unit", "H", "E1", "pt"]},
    "X2": {"coordinates": ["E1", "E2", "L"], "weights": [1, 1, 1],
           "labels": ["unit", "H", "E1", "E2", "pt"]},
}


def requests_for(target):
    spec = TARGETS[target]
    requests = []
    for beta in itertools.product(range(5), repeat=len(spec["weights"])):
        energy = sum(w * b for w, b in zip(spec["weights"], beta))
        if not 0 < energy <= 4:
            continue
        for count in range(3):
            for labels in itertools.product(spec["labels"], repeat=count):
                codimension = sum(0 if a == "unit" else 2 if a == "pt" else 1 for a in labels)
                for powers in itertools.product(range(8), repeat=count):
                    if sum(powers) + codimension == energy + 1 + count:
                        requests.append((beta, powers, labels))
    return requests


def manifest():
    targets = []
    for target, spec in TARGETS.items():
        queries = requests_for(target)
        targets.append({
            "target": target, "curve_coordinates": spec["coordinates"],
            "energy_weights": spec["weights"], "basis_labels": spec["labels"],
            "request_count": len(queries),
            "counts_by_arity": {str(n): sum(len(p) == n for _, p, _ in queries) for n in range(3)},
            "requests": [{"target": target, "genus": 2, "class": list(b),
                          "powers": list(p), "labels": list(a)} for b, p, a in queries],
        })
    return {"schema_version": 1, "kind": "axiomatic_gw.genus_two_few_markings.requests",
            "genus": 2, "positive_energy_bound": 4, "maximum_markings": 2,
            "dimension_equation": "sum(psi + complex_codimension) = energy + genus - 1 + n",
            "ordered_markings": True, "request_count": sum(t["request_count"] for t in targets),
            "targets": targets,
            "status": "Request manifest only; no numerical values or reconstruction acceptance"}


def manifest_text(result):
    """Keep each complete request on one line for reviewable corpus diffs."""
    header = {k: v for k, v in result.items() if k != "targets"}
    lines = [json.dumps(header, sort_keys=True, indent=2)[:-2] + ",", '  "targets": [']
    for index, target in enumerate(result["targets"]):
        metadata = {k: v for k, v in target.items() if k != "requests"}
        lines.extend("    " + line for line in json.dumps(metadata, sort_keys=True, indent=2)[:-2].splitlines())
        lines[-1] += ","
        lines.append('      "requests": [')
        for i, query in enumerate(target["requests"]):
            lines.append("        " + json.dumps(query, sort_keys=True, separators=(",", ":")) +
                         ("," if i + 1 < len(target["requests"]) else ""))
        lines.extend(["      ]", "    }" + ("," if index + 1 < len(result["targets"]) else "")])
    lines.extend(["  ]", "}", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = manifest()
    text = manifest_text(result)
    if args.check:
        if args.output.read_text() != text:
            raise ValueError("The full held few-marking manifest changed")
    else:
        args.output.write_text(text)
    print("Held ordered requests:", {t["target"]: t["request_count"] for t in result["targets"]})


if __name__ == "__main__":
    main()
