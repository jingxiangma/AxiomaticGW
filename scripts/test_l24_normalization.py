#!/usr/bin/env python3
"""Offline arithmetic/graph-operation regression for the exploratory L24 candidate.

This is a Python check, not Lean certification of the L24 geometric equation.
The higher-power inputs are the separately replayed fixed psi pullbacks.
"""
import copy
from fractions import Fraction
from itertools import combinations, permutations
import json
from pathlib import Path
import unittest

from export_admcycles_certificate import require
from export_genus_two_psi_pullbacks import PRODUCER_PINS, SOURCE_PINS
from search_l24_normalization import boundary, decorations, flags, key, power, primitive, replace_raw

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/l24-normalization-exploration.json"


def sparse(rows):
    result = {}
    for i, (a, b) in rows:
        require(i not in result and b > 0 and a != 0, "Malformed sparse coordinates")
        result[i] = Fraction(a, b)
    return result


def accumulate(row, i, q):
    row[i] = row.get(i, 0) + q
    if not row[i]:
        del row[i]


def pad(g):
    return dict(g, kappa=[list(p) + [0] * (3-len(p)) for p in g["kappa"]])


def relabel(g, inverse):
    return dict(g, leg_vertices=[g["leg_vertices"][i] for i in inverse],
                leg_psi=[g["leg_psi"][i] for i in inverse])


def validate(report):
    require(report["source_sha256"] == SOURCE_PINS and report["producer_sha256"] == PRODUCER_PINS,
            "Changed provenance")
    require(report["normalization"] == "raw_gluing_pushforward", "Changed normalization")
    graphs = report["graphs"]
    keys = {key(g): i for i, g in enumerate(graphs)}
    require(len(keys) == len(graphs) == 2090, "Changed frame")
    perms = [[p[0], 1, p[1], p[2]] for p in permutations([0, 2, 3])]
    require(report["permutations"] == perms, "Changed averaging group")

    def average(row):
        out = {}
        for i, q in row.items():
            for perm in perms:
                accumulate(out, keys[key(relabel(graphs[i], perm))], q / 6)
        return out

    frames = {2: json.loads((ROOT / "environments/genus-two-psi-product-exploration.json").read_text()),
              3: json.loads((ROOT / "environments/belorousski-pandharipande.json").read_text())}
    pulls = json.loads((ROOT / "environments/genus-two-psi-pullbacks-exploration.json").read_text())
    source_rows = {("square", 2): pulls["cases"][0]["coordinates"],
                   ("square", 3): pulls["cases"][1]["coordinates"],
                   ("product", 3): pulls["cases"][2]["coordinates"],
                   ("product", 2): frames[2]["requested"]}
    current = sparse(report["initial"])
    for step in report["steps"]:
        g, v = graphs[step["base"]], step["vertex"]
        fs = flags(g, v)
        n = len(fs)
        row = {}
        if step["kind"] in ("square", "product"):
            order = step["order"]
            require(sorted(order) == list(range(n)), "Invalid source permutation")
            inv = [order.index(i) for i in range(n)]
            for c, source in zip(source_rows[step["kind"], n], frames[n]["graphs"]):
                if c[0]:
                    out = replace_raw(g, v, relabel(pad(source), inv))
                    accumulate(row, keys[key(out)], Fraction(*c))
        else:
            require(step["kind"] == "rational_psi" and g["genus"][v] == 0,
                    "Wrong rational operation")
            a = step["flag"]
            b, c = step["anchors"]
            require(len({a, b, c}) == 3, "Repeated anchors")
            ps = [power(g, f) for f in fs]
            require(ps[a] > 0, "No cotangent factor to reduce")
            ps[a] -= 1
            row[step["base"]] = Fraction(1)
            rest = [j for j in range(n) if j not in (a, b, c)]
            for size in range(1, len(rest)+1):
                for subset in combinations(rest, size):
                    out = replace_raw(g, v, boundary(n, {a, *subset}), ps)
                    accumulate(row, keys[key(out)], -1)
        require(row == sparse(step["row"]), "Operation provenance differs")
        weight = Fraction(*step["weight"])
        require(row.get(step["base"]) == 1 and current.get(step["base"]) == -weight,
                "Reduction does not cancel the selected term")
        for i, q in row.items():
            accumulate(current, i, weight*q)
    current = average(current)
    require(Fraction(*report["normalization_scale"]) == 1, "Changed initial scale")
    for step in report["wdvv"]:
        g, v = step["graph"], step["vertex"]
        require(g["genus"][v] == 0 and len(flags(g, v)) == 4 and decorations(g, v) == 0,
                "Not an undecorated four-point rational component")
        channels = ({0, 1}, {0, 2}, {0, 3})
        require(step["channel"] in (1, 2), "Wrong channel")
        row = {}
        for a, sign in ((channels[0], 1), (channels[step["channel"]], -1)):
            out = replace_raw(g, v, boundary(4, a))
            accumulate(row, keys[key(out)], Fraction(sign))
        row = average(row)
        require(row == sparse(step["row"]), "WDVV image differs")
        for i, q in row.items():
            accumulate(current, i, Fraction(*step["weight"])*q)
    require(current == sparse(report["full"]), "Full correction sum differs")
    target = sparse(report["primitive"])
    require({i: q for i, q in current.items() if primitive(graphs[i])} == target,
            "Primitive part differs")
    require(len(current) == 721 and len(target) == 18, "Incomplete retained support")
    require(all(not any(any(k) for k in graphs[i]["kappa"]) and
                all(h < 2 or decorations(graphs[i], v) <= 1
                    for v, h in enumerate(graphs[i]["genus"])) for i in current),
            "High genus-two powers remain")
    return current


class L24NormalizationTests(unittest.TestCase):
    def setUp(self):
        self.report = json.loads(REPORT.read_text())

    def test_complete_operation_derivation(self):
        self.assertEqual(len(validate(self.report)), 721)
        self.assertEqual(self.report["native_substitution_checks"], 1516)
        self.assertEqual(self.report["intersection_diagnostics"], [[0, 1]]*3)

    def test_rejects_changed_operations_and_omitted_corrections(self):
        mutations = [lambda d: d["full"].pop(),
                     lambda d: d["steps"][0]["weight"].__setitem__(0, 0),
                     lambda d: d["steps"][0]["order"].reverse(),
                     lambda d: d["steps"][0]["row"][0][1].__setitem__(0, 2),
                     lambda d: d["wdvv"][0].update(channel=1),
                     lambda d: d["permutations"].pop(),
                     lambda d: d.update(normalization_scale=[2, 1])]
        for mutate in mutations:
            changed = copy.deepcopy(self.report)
            mutate(changed)
            with self.assertRaises((ValueError, KeyError)):
                validate(changed)


if __name__ == "__main__":
    unittest.main(verbosity=2)
