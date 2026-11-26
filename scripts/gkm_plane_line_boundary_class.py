#!/usr/bin/env python3
"""Export a degree-one plane fixed-locus class and its unit pullback before integration."""

import argparse
import ast
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
import tempfile

from export_admcycles_certificate import unique_object
from export_gkm_inputs import ROOT, producer_source, require, target_specifications

DEFAULT = ROOT / "environments/gkm-plane-line-boundary-class.json"
LEAN = ROOT / "AxiomaticGW/GKM/Fixtures/PlaneLineBoundaryData.lean"


def explore(producer, source, *, blowups=0, exceptional=0):
    from sage.all import Fan, LaurentPolynomialRing, PolynomialRing, QQ, ZZ, matrix, prod, vector
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing
    from admcycles import admcycles, stable_graph, tautological_ring

    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review Sage/admcycles version")
    pins = json.loads((ROOT / "environments/genus-one-psi-exploration.json").read_text())
    for module in (admcycles, stable_graph, tautological_ring):
        path = Path(module.__file__)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == pins["producer_source_sha256"][path.name],
                f"Changed admcycles source {path.name}")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapsGKM, toric_target_from_fan

    require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
            "Imported another producer")
    spec = target_specifications()[blowups]
    ring = LaurentPolynomialRing(ZZ, names=("x", "y"))
    field = PolynomialRing(QQ, names=("x", "y")).fraction_field()
    target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), ring,
                                   curve_basis=spec["curves"], name=spec["id"])
    points = sorted(target.fixed_points())

    def divisor(ray):
        def value(pt):
            if ray not in pt:
                return ring.zero()
            dual = matrix([spec["rays"][j] for j in pt]).transpose().inverse()
            return sum(c * t for c, t in zip(dual.row(pt.index(ray)), ring.gens()))
        return {pt: value(pt) for pt in points}

    d0, d1, d2 = [divisor(ray) for ray in range(3)]
    def points_at(a, b):
        return {pt: a[pt] * b[pt] for pt in points}
    unit = {pt: ring.one() for pt in points}
    point = points_at(d0, d2)
    hyperplane = {pt: sum(divisor(ray)[pt] for ray in spec["hyperplane"]) for pt in points}
    node_basis = [unit, hyperplane] + [divisor(ray) for ray in spec["exceptional"]] + [point]
    extra = {}
    if not blowups:
        require(points == [(0, 1), (0, 2), (1, 2)], "Changed plane fan")
        p, q, _ = points
        lifts = [points_at(d0, d1), d1, point, d2, unit]
        require(all(lifts[0][pt] == (prod(target.tangent_space_cohom(p)) if pt == p else 0)
                    and lifts[2][pt] == (prod(target.tangent_space_cohom(q)) if pt == q else 0)
                    for pt in points), "Incorrect fixed-point lifts")
        target_label, curve, lift_names = "plane", [1], ["D0*D1", "D1", "D0*D2", "D2"]
    else:
        ray = spec["exceptional"][exceptional]
        p, q = [pt for pt in points if ray in pt]
        right_ray, = set(q) - set(p)
        own = divisor(ray)
        left = {pt: own[pt] - own[q] for pt in points}
        right = {pt: own[pt] - own[p] for pt in points}
        lifts = [left, left, right, divisor(right_ray), unit]
        target_label = "hirzebruchOne" if blowups == 1 else "blowupTwo"
        curve = list(spec["curves"][(ray,)])
        require(curve == [int(j == exceptional) for j in range(blowups + 1)] and
                target.curve_class(p, q) == vector(ZZ, curve) and
                [record[2] for record in target.curve_normal_bundle(p, q)] == [-1],
                "Target curve or its O(-1) normal bundle changed")
        lift_names = [f"D{ray}-D{ray}(q)"] * 2 + [f"D{ray}-D{ray}(p)", f"D{right_ray}"]
        frame = matrix(field, [[row[pt] for row in node_basis] for pt in points])
        coordinates = [frame.solve_right(vector(field, [lift[pt] for pt in points]))
                       for lift in lifts[:4]]
        ordinary = []
        for column in coordinates:
            v = []
            for entry in column:
                require(entry.denominator()(0, 0) != 0, "Insertion coordinates have a pole")
                val = entry.numerator()(0, 0) / entry.denominator()(0, 0)
                require(val in ZZ, "Nonintegral toric divisor")
                v.append(int(val))
            ordinary.append(v)
        extra = {"fixed_points": [[int(i) for i in pt] for pt in (p, q)],
                 "normal_degree": -1, "ordinary_insertions": ordinary,
                 "equivariant_insertions": [[str(entry) for entry in col] for col in coordinates]}
    maps = StableMapsGKM(target)
    beta = (ZZ ** len(curve))(curve)
    records, boundary = {}, {}
    correction = {}
    for n in (4, 5):
        insertions = [(0, target.cohomology_class(lift)) for lift in lifts[:n]]
        loci = maps.fixed_loci(0, n, beta)
        kept = []
        for locus in loci:
            if any(not f(locus.marked_point_image(i)) for i, (_, f) in enumerate(insertions, 1)):
                continue
            factors = locus._localization_factors(insertions)
            vertices = sorted(locus.vertices(), key=locus.image)
            require([locus.image(v) for v in vertices] == [p, q] and len(locus.edges()) == 1
                    and locus.edge_degree(locus.edges()[0]) == 1, "Unexpected map components")
            groups = [sorted(int(m) for m in locus.marked_points(v)) for v in vertices]
            require(all(len(group) >= 2 and locus.genus(v) == 0 and len(locus.edges(v)) == 1
                        for v, group in zip(vertices, groups)), "Unstable contracted source")
            source_vertices = {row["vertex"]: row for row in factors["source_vertices"]}
            weights = [field(source_vertices[v]["incident_edge_weights"][0]) for v in vertices]
            eulers = [field(prod(source_vertices[v]["target_weights"])) for v in vertices]
            parts = [field(factors[key]) for key in
                     ("edge_contribution", "tangent_normalization", "insertion_factor")]
            aut = int(factors["automorphism_denominator"])
            # Genus zero: lambda_0=1 at every target weight. Keep all flag powers
            # through the dimension of each contracted vertex, including the constant.
            coeff = prod(parts) / (aut * prod(eulers) * prod(weights))
            require(weights[0] == -weights[1] and aut == 1, "Changed line or automorphism")
            flags = [n + 1, n + 2]
            graph = StableGraph([0, 0], [g + [flag] for g, flag in zip(groups, flags)], [tuple(flags)])
            tag = "base" if n == 4 else ("left" if 5 in groups[0] else "right")
            require(tag not in boundary, "Duplicate marking distribution")
            boundary[tag] = graph.boundary_pushforward()
            term = {"marks": groups, "edge": str(parts[0]), "tangent": str(parts[1]),
                    "insertions": str(parts[2]), "automorphism": aut,
                    "eulers": list(map(str, eulers)), "flags": list(map(str, weights)),
                    "boundary": str(coeff)}
            require(coeff == (-1 if blowups else 1), "Changed primitive-curve class coefficient")
            if n == 5:
                unit_side = int(5 in groups[1])
                classes = [TautologicalRing(0, len(g) + 1) for g in groups]
                inputs = [c.fundamental_class() for c in classes]
                node = len(groups[unit_side]) + 1
                inputs[unit_side] = classes[unit_side].psi(node)
                correction[tag] = graph.boundary_pushforward(inputs)
                term["node_psi"] = str(coeff / weights[unit_side])
                require(field(factors["total"]) == coeff / weights[unit_side],
                        "Top-degree check disagrees with native integrated contribution")
            else:
                require(field(factors["total"]) == coeff, "Incorrect base class integral")
            kept.append(term)
        expected = [[[1, 2], [3, 4]]] if n == 4 else [[[1, 2], [3, 4, 5]], [[1, 2, 5], [3, 4]]]
        kept.sort(key=lambda record: record["marks"])
        require([record["marks"] for record in kept] == expected and
                len(loci) == (1 if blowups else 3) * 2 ** n,
                "Incomplete fixed-locus or marking coverage")
        records[str(n)] = {"enumerated": len(loci), "nonzero_loci": kept}

    central = StableGraph([0, 0, 0], [[1, 2, 6], [7, 5, 8], [9, 3, 4]], [(6, 7), (8, 9)])
    common = central.boundary_pushforward()
    for value in correction.values():
        require((value - common).is_zero(), "Flag psi differs from the common trivalent refinement")
    require((boundary["base"].forgetful_pullback([5]) - boundary["left"] -
             boundary["right"]).vector(1).is_zero(), "Incorrect raw unit pullback")
    require(common.evaluate() == boundary["base"].evaluate() == 1, "Wrong stack multiplicity")
    # The boundary that bubbles off the fifth unit with the first insertion is a
    # section of the forgetful map. Its remaining 4-point factor is Mbar_{0,4}.
    section = StableGraph([0, 0], [[1, 5, 6], [7, 2, 3, 4]], [(6, 7)])
    actual = section.boundary_pullback(boundary["left"] + boundary["right"])

    def four_point_factor(product):
        r4 = TautologicalRing(0, 4)
        return sum((a.to_tautological_class().evaluate() * b.to_tautological_class()
                    for a, b in product.terms), r4.zero())

    require((four_point_factor(actual) - boundary["base"]).vector(1).is_zero(),
            "Nonzero separating restriction differs on the four-point factor")
    # Both effective degree splittings at this boundary enter the CohFT equation.
    # Compute the three-point tail independently with the producer, for every node state.
    tail, localized_tail = [], []
    for degree in (0, 1):
        row, localized = [], []
        for node in node_basis:
            args = [(0, target.cohomology_class(lift)) for lift in (lifts[0], lifts[4], node)]
            value = field(maps.integrate(0, 3, degree * beta, args))
            require(value.denominator()(0, 0) != 0, "Unresolved three-point tail pole")
            val = QQ(value.numerator()(0, 0) / value.denominator()(0, 0))
            require(val in ZZ, "Nonintegral ordinary tail")
            row.append(int(val))
            localized.append(str(value))
        tail.append(row)
        localized_tail.append(localized)
    if blowups:
        expected = [0] * len(node_basis)
        expected[exceptional + 2] = -1
        require(tail == [expected, [0] * len(node_basis)], "Changed exceptional tail")
        extra["equivariant_tail"] = localized_tail
    else:
        require(localized_tail == [["1", "0", "0"], ["0"] * 3], "Changed plane tail")
    return {"source": source["revision"], "sage": version, "admcycles": "1.4",
            "target": target_label, "genus": 0, "curve": curve, "lifts": lift_names, **extra,
            "unit_mark": 5, "tail_primary": tail, "loci": records,
            "common_refinement": [[1, 2], [5], [3, 4]]}


def lean_expression(text):
    """Decode only polynomial arithmetic and exact fractions in the two pinned characters."""
    operators = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/", ast.Pow: "^"}

    def convert(node):
        if isinstance(node, ast.Name) and node.id in ("x", "y"):
            return node.id
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return str(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return f"(-{convert(node.operand)})"
        if isinstance(node, ast.BinOp) and type(node.op) in operators:
            return f"({convert(node.left)} {operators[type(node.op)]} {convert(node.right)})"
        raise ValueError("Unsupported symbolic expression")
    return convert(ast.parse(text.replace("^", "**"), mode="eval").body)


def lean_data(report):
    base, = report["loci"]["4"]["nonzero_loci"]
    right, left = report["loci"]["5"]["nonzero_loci"]
    for field in ("edge", "tangent", "insertions", "eulers", "flags", "automorphism", "boundary"):
        require(base[field] == right[field] == left[field], f"Arity changes {field}")
    lines = ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.", "Authors: JMA",
             "-/", "module", "", "public import AxiomaticGW.GKM.EquivariantCoefficients",
             "public import Mathlib.Data.Fin.VecNotation", "", "/-!",
             "# Fixed-locus data for a degree-one line in the plane",
             "", "Generated by `scripts/gkm_plane_line_boundary_class.py` from the pinned producer.",
             "All three surviving loci share their edge, two vertex, insertion and stabilizer factors.",
             "-/", "", "@[expose] public section", "namespace AxiomaticGW.GKM.PlaneLineBoundaryData",
             "open EquivariantCoefficients", "", "noncomputable section", ""]
    for label, values in (("baseLeg", base), ("leftLeg", left), ("rightLeg", right)):
        groups = values["marks"]
        labels = sorted(item for group in groups for item in group)
        require(labels == list(range(1, len(labels) + 1)), "Lost or duplicated marking")
        frame = ", ".join(str(next(i for i, group in enumerate(groups) if item in group))
                          for item in labels)
        lines.extend(["/-- Contracted endpoint of each external marking, in request order. -/",
                      f"def {label} : Fin {len(labels)} → Fin 2 := ![{frame}]", ""])
    require(len(report["tail_primary"]) == 2 and all(len(row) == 3 for row in report["tail_primary"]),
            "Missing three-point node state or degree split")
    for i, row in enumerate(report["tail_primary"]):
        require(all(type(v) is int for v in row), "Invalid tail value")
        frame = ", ".join(str(v) for v in row)
        lines.extend([f"/-- Native three-point tail at degree {i}, in unit, H, pt order. -/",
                      f"def tail{i} : Fin 3 → ℚ := ![{frame}]", ""])
    for label, expr in (("edge", base["edge"]), ("tangent", base["tangent"]),
                        ("insertions", base["insertions"]), ("eulerLeft", base["eulers"][0]),
                        ("eulerRight", base["eulers"][1]), ("flagLeft", base["flags"][0]),
                        ("flagRight", base["flags"][1]), ("automorphism", str(base["automorphism"])),
                        ("baseClaim", base["boundary"]), ("psiLeft", left["node_psi"]),
                        ("psiRight", right["node_psi"])):
        lines.extend([f"/-- Exact incoming {label} coefficient. -/",
                      f"def {label} : Coefficient :=", f"  {lean_expression(expr)}", ""])
    return "\n".join(lines + ["end", "", "end AxiomaticGW.GKM.PlaneLineBoundaryData", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--producer", type=Path)
    source.add_argument("--replay", type=Path, help="Render the saved exchange without Sage")
    parser.add_argument("--lean-output", type=Path, default=LEAN)
    parser.add_argument("--output", type=Path, default=DEFAULT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.replay:
        data = json.loads(args.replay.read_text(), object_pairs_hook=unique_object)
    else:
        producer, pin = producer_source(args.producer)
        with tempfile.TemporaryDirectory(prefix="gkm-plane-line-class-") as temp:
            for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
                path = Path(temp) / name
                path.mkdir()
                os.environ[name] = str(path)
            (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
            data = explore(producer, pin)
        report = json.dumps(data, indent=2, sort_keys=True) + "\n"
        if args.check:
            require(args.output.read_text() == report, "Held fixed-locus report differs")
        else:
            args.output.write_text(report)
    pin = json.loads((ROOT / "environments/gkm-localization-source.json").read_text())
    require(data["source"] == pin["revision"] and data["target"] == "plane" and
            data["sage"] == "10.9" and data["admcycles"] == "1.4" and
            data["genus"] == 0 and data["curve"] == [1] and data["unit_mark"] == 5 and
            data["lifts"] == ["D0*D1", "D1", "D0*D2", "D2"] and
            data["common_refinement"] == [[1, 2], [5], [3, 4]] and
            [data["loci"][str(n)]["enumerated"] for n in (4, 5)] == [48, 96],
            "Changed request, degree, source, enumeration or graph frame")
    lean = lean_data(data)
    if args.check:
        require(args.lean_output.read_text() == lean, "Held Lean data differs")
    else:
        args.lean_output.write_text(lean)


if __name__ == "__main__":
    main()
