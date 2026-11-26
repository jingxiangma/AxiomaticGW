#!/usr/bin/env python3
"""Independently check the version-one GKM input bundle with Python alone.

Sparse polynomial arithmetic over Fraction verifies symbolic identities by
cross multiplication; it does not use Sage's matrix or polynomial routines.
The numerical regression requests and expected values are fixed here, not
read from the producer's requested claims. This is supplemental validation,
not Lean proof replay or a geometric CohFT comparison theorem.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
ONE = {(0, 0): Fraction(1)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value):
    require(type(value) is int, "Expected an exact integer")
    return value


def rational(value):
    require(isinstance(value, list) and len(value) == 2, "Malformed rational")
    a, b = map(integer, value)
    require(b > 0, "Nonpositive rational denominator")
    return Fraction(a, b)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def polynomial(terms):
    require(isinstance(terms, list), "Expected sparse polynomial terms")
    result = {}
    for term in terms:
        require(isinstance(term, list) and len(term) == 2, "Malformed polynomial term")
        powers, coefficient = term
        require(isinstance(powers, list) and len(powers) == 2, "Wrong polynomial arity")
        powers = tuple(map(integer, powers))
        coefficient = rational(coefficient)
        require(all(p >= 0 for p in powers) and powers not in result and coefficient != 0,
                "Negative/repeated exponent or sparse zero coefficient")
        result[powers] = coefficient
    require(list(result) == sorted(result), "Unsorted polynomial terms")
    return result


def add_polynomials(a, b):
    result = dict(a)
    for powers, coefficient in b.items():
        result[powers] = result.get(powers, Fraction(0)) + coefficient
        if result[powers] == 0:
            del result[powers]
    return result


def multiply_polynomials(a, b):
    result = {}
    for (i, j), c in a.items():
        for (k, l), d in b.items():
            powers = (i + k, j + l)
            result[powers] = result.get(powers, Fraction(0)) + c * d
    return {powers: coefficient for powers, coefficient in result.items() if coefficient}


class RationalFunction:
    def __init__(self, numerator, denominator=ONE):
        require(bool(denominator), "Zero polynomial denominator")
        self.numerator = numerator
        self.denominator = denominator if numerator else ONE

    @staticmethod
    def constant(value):
        value = Fraction(value)
        return RationalFunction({(0, 0): value} if value else {})

    @staticmethod
    def from_json(value):
        require(isinstance(value, dict) and set(value) == {
            "numerator", "denominator", "denominator_nonzero_term"}, "Malformed rational function")
        numerator = polynomial(value["numerator"])
        denominator = polynomial(value["denominator"])
        witness = polynomial([value["denominator_nonzero_term"]])
        require(bool(witness) and all(denominator.get(p) == c for p, c in witness.items()),
                "Invalid denominator nonzero coefficient witness")
        return RationalFunction(numerator, denominator)

    def __add__(self, other):
        if not isinstance(other, RationalFunction):
            other = RationalFunction.constant(other)
        if self.denominator == other.denominator:
            return RationalFunction(add_polynomials(self.numerator, other.numerator), self.denominator)
        return RationalFunction(add_polynomials(
            multiply_polynomials(self.numerator, other.denominator),
            multiply_polynomials(other.numerator, self.denominator)),
            multiply_polynomials(self.denominator, other.denominator))

    __radd__ = __add__

    def __mul__(self, other):
        if not isinstance(other, RationalFunction):
            other = RationalFunction.constant(other)
        return RationalFunction(multiply_polynomials(self.numerator, other.numerator),
                                multiply_polynomials(self.denominator, other.denominator))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, RationalFunction):
            other = RationalFunction.constant(other)
        return self * RationalFunction(other.denominator, other.numerator)

    def __eq__(self, other):
        if not isinstance(other, RationalFunction):
            other = RationalFunction.constant(other)
        return multiply_polynomials(self.numerator, other.denominator) == \
            multiply_polynomials(other.numerator, self.denominator)

    def ordinary(self):
        denominator = self.denominator.get((0, 0), Fraction(0))
        require(denominator != 0, "Specialization representative has a pole at zero")
        return self.numerator.get((0, 0), Fraction(0)) / denominator


def matrix(values, size):
    require(isinstance(values, list) and len(values) == size and
            all(isinstance(row, list) and len(row) == size for row in values), "Wrong matrix shape")
    return [[RationalFunction.from_json(value) for value in row] for row in values]


def check_inverse(a, b):
    size = len(a)
    for left, right in [(a, b), (b, a)]:
        require(all(sum(left[i][k] * right[k][j] for k in range(size)) == int(i == j)
                    for i in range(size) for j in range(size)), "Failed two-sided matrix inverse")


def character(values):
    require(isinstance(values, list) and len(values) == 2, "Wrong character arity")
    values = list(map(integer, values))
    return RationalFunction({p: Fraction(c) for p, c in zip([(1, 0), (0, 1)], values) if c})


def fixed_fan(exceptional_count):
    """Independent fixed toric presentations, not supplied by candidate data."""
    rays = [[1, 0], [0, 1], [-1, -1]]
    cones = [[0, 1], [0, 2], [1, 2]]
    if exceptional_count >= 1:
        rays.append([1, 1])
        cones = [[0, 2], [0, 3], [1, 2], [1, 3]]
    if exceptional_count == 2:
        rays.append([-1, 0])
        cones = [[0, 2], [0, 3], [1, 3], [1, 4], [2, 4]]
    return rays, cones


def dual_characters(rays, cone):
    """Dual characters of a smooth two-dimensional cone, by its determinant."""
    (a, b), (c, d) = [rays[rho] for rho in cone]
    determinant = a * d - b * c
    require(abs(determinant) == 1, "Nonsmooth toric cone")
    return [[d // determinant, -c // determinant], [-b // determinant, a // determinant]]


def check_target(frame, target_id, exceptional_count, energy, curve_map):
    size = exceptional_count + 3
    require(frame["target"] == target_id and frame["basis"] ==
            ["unit", "H"] + [f"E{i+1}" for i in range(exceptional_count)] + ["pt"],
            "Wrong target or state basis")
    require(list(map(integer, frame["energy_weights"])) == energy and
            [[integer(c) for c in row] for row in frame["curve_to_signed_lattice"]] == curve_map,
            "Wrong energy or curve-class transport")
    rays, points = fixed_fan(exceptional_count)
    require([[integer(c) for c in ray] for ray in frame["rays"]] == rays and
            [[integer(rho) for rho in p] for p in frame["points"]] == points,
            "Changed fixed toric presentation")
    tangent = [dual_characters(rays, p) for p in points]
    require(len(frame["tangent_characters"]) == size and
            all(sorted([list(map(integer, w)) for w in weights]) == sorted(expected)
                for weights, expected in zip(frame["tangent_characters"], tangent)),
            "Tangent characters disagree with the dual fan cones")
    divisors = [[character(tangent[p][cone.index(rho)]) if rho in cone
                 else RationalFunction.constant(0) for p, cone in enumerate(points)]
                for rho in range(len(rays))]
    require(len(frame["euler"]) == size, "Wrong Euler-vector length")
    euler = [RationalFunction.from_json(value) for value in frame["euler"]]
    for i, weights in enumerate(frame["tangent_characters"]):
        require(len(weights) == 2 and bool(euler[i].numerator) and
                character(weights[0]) * character(weights[1]) == euler[i],
                "Euler factor does not match the tangent characters")
    B = matrix(frame["basis_to_fixedpoint"], size)
    inverse = matrix(frame["fixedpoint_to_basis"], size)
    metric = matrix(frame["metric"], size)
    inverse_metric = matrix(frame["inverse_metric"], size)
    check_inverse(B, inverse)
    check_inverse(metric, inverse_metric)
    require(all(B[p][0] == 1 for p in range(size)), "Flat unit is not the constant function")
    hyperplane_rays = [0, 3] if exceptional_count == 2 else [2]
    for p in range(size):
        lifts = [RationalFunction.constant(1), sum(divisors[rho][p] for rho in hyperplane_rays)]
        lifts += [divisors[rho][p] for rho in range(3, 3 + exceptional_count)]
        lifts += [divisors[0][p] * divisors[2][p]]
        require(all(B[p][i] == lift for i, lift in enumerate(lifts)),
                "Basis restrictions disagree with the fixed toric divisor lifts")
    for i in range(size):
        for j in range(size):
            require(sum(B[p][i] * B[p][j] / euler[p] for p in range(size)) == metric[i][j],
                    "Metric is not the localization trace pairing")
            require(sum(inverse[i][p] * euler[p] * inverse[j][p] for p in range(size)) ==
                    inverse_metric[i][j], "Incorrect inverse metric transport")
            expected_metric = int((i, j) in [(0, size-1), (size-1, 0), (1, 1)])
            if i == j and 2 <= i < size-1:
                expected_metric = -1
            require(metric[i][j].ordinary() == expected_metric and
                    rational(frame["ordinary_metric"][i][j]) == expected_metric,
                    "Ordinary surface metric disagrees")
    products = frame["products"]
    ordinary_products = frame["ordinary_products"]
    require(len(products) == size and len(ordinary_products) == size and
            all(len(row) == size for row in products + ordinary_products), "Wrong product shape")
    for i in range(size):
        for j in range(size):
            require(len(products[i][j]) == len(ordinary_products[i][j]) == size,
                    "Wrong product coefficient count")
            coefficients = [RationalFunction.from_json(c) for c in products[i][j]]
            require(all(sum(B[p][k] * coefficients[k] for k in range(size)) == B[p][i] * B[p][j]
                        for p in range(size)), "Product is not pointwise multiplication")
            expected = [0] * size
            if i == 0:
                expected[j] = 1
            elif j == 0:
                expected[i] = 1
            elif i == j and 1 <= i < size-1:
                expected[size-1] = 1 if i == 1 else -1
            require([c.ordinary() for c in coefficients] == expected and
                    [rational(c) for c in ordinary_products[i][j]] == expected,
                    "Ordinary surface product disagrees")
    c1 = [RationalFunction.from_json(c) for c in frame["c1_coordinates"]]
    require(len(c1) == size and [c.ordinary() for c in c1] ==
            [0, 3] + [-1] * exceptional_count + [0], "Ordinary first Chern class disagrees")
    require(all(sum(B[p][k] * c1[k] for k in range(size)) ==
                sum(character(w) for w in frame["tangent_characters"][p]) for p in range(size)),
            "First Chern restrictions disagree with tangent characters")
    intersections = frame["divisor_curve_intersections"]
    require(len(intersections) == exceptional_count + 1 and
            all(len(row) == len(rays) for row in intersections), "Wrong divisor-intersection shape")
    intersections = [[rational(c) for c in row] for row in intersections]
    for i, row in enumerate(intersections):
        for rho, value in enumerate(row):
            require(sum(B[p][i+1] * divisors[rho][p] / euler[p] for p in range(size)) == value,
                    "Divisor intersections disagree with the localization trace")
    generator_walls = [0] if exceptional_count == 0 else [3, 0] if exceptional_count == 1 else [3, 4, 1]
    derived_map = [[intersections[0][rho] for rho in generator_walls]]
    derived_map += [[-row[rho] for rho in generator_walls] for row in intersections[1:]]
    require(derived_map == curve_map, "Curve transport disagrees with divisor intersections")
    outgoing = [[] for _ in range(size)]
    edge_weights = {}
    expected_edges = {(p, q) for p in range(size) for q in range(p+1, size)
                      if len(set(points[p]).intersection(points[q])) == 1}
    seen_edges = set()
    for edge in frame["edges"]:
        p, q = integer(edge["source"]), integer(edge["target"])
        require(0 <= p < size and 0 <= q < size and p != q, "Invalid edge endpoints")
        weight = list(map(integer, edge["weight"]))
        character(weight)
        pair = tuple(sorted((p, q)))
        require(pair in expected_edges and pair not in seen_edges, "Changed or repeated toric edge")
        seen_edges.add(pair)
        wall = sorted(set(points[p]).intersection(points[q]))
        require(list(map(integer, edge["wall"])) == wall, "Edge wall disagrees with its endpoints")
        transverse_ray = next(rho for rho in points[p] if rho not in wall)
        require(weight == tangent[p][points[p].index(transverse_ray)],
                "Edge character disagrees with the oriented fan edge")
        edge_weights[p, q] = weight
        edge_weights[q, p] = [-c for c in weight]
        outgoing[p].append(weight)
        outgoing[q].append([-c for c in weight])
        beta = list(map(integer, edge["class"]))
        require(len(beta) == len(energy) and all(c >= 0 for c in beta), "Invalid curve coordinates")
        require(all(sum(c * b for c, b in zip(row, beta)) ==
                    intersections[i][wall[0]] * (1 if i == 0 else -1)
                    for i, row in enumerate(curve_map)),
                "Edge class disagrees with its divisor intersections")
        normal = edge["normal_bundles"]
        require(len(normal) == 1 and len(normal[0]) == 3, "Wrong normal-bundle rank")
        u, v, degree = map(integer, normal[0])
        require(0 <= u < size and 0 <= v < size and
                sum(w * c for w, c in zip(energy, beta)) == 2 + degree,
                "Curve energy disagrees with tangent/normal degrees")
    require(seen_edges == expected_edges, "Missing toric edge")
    require(all(sorted(weights) == sorted(frame["tangent_characters"][p])
                for p, weights in enumerate(outgoing)), "Edge weights do not reproduce the tangent spaces")
    for edge in frame["edges"]:
        p, q = edge["source"], edge["target"]
        u, v, degree = edge["normal_bundles"][0]
        require((p, u) in edge_weights and (q, v) in edge_weights and u != q and v != p,
                "Normal-bundle branches are not the other incident edges")
        require(all(a - b == degree * c for a, b, c in
                    zip(edge_weights[p, u], edge_weights[q, v], edge_weights[p, q])),
                "Normal-bundle degree disagrees with character differences")
    zero = [0] * len(energy)
    expected_queries = [(1, zero, [(0, 1)], Fraction(-1, 8)),
                        (2, zero, [(1, 1)], Fraction(-1, 960))]
    if target_id == "X0":
        expected_queries.append((0, [1], [(0, size-1)] * 2, Fraction(1)))
    elif target_id == "X1":
        expected_queries.append((0, [0, 1], [(0, size-1)], Fraction(1)))
    else:
        expected_queries.append((0, [1, 0, 0], [], Fraction(1)))
    require(len(frame["queries"]) == len(expected_queries), "Missing fixed regression requests")
    for query, (genus, beta, insertions, expected) in zip(frame["queries"], expected_queries):
        require(integer(query["genus"]) == genus and list(map(integer, query["class"])) == beta,
                "Changed regression genus or curve class")
        require(query["insertions"] == [{"label": i, "psi": k, "basis": b}
                                      for i, (k, b) in enumerate(insertions)], "Changed regression insertions")
        for insertion in query["insertions"]:
            for value in insertion.values():
                integer(value)
        require(type(query["curve_stable"]) is bool and
                query["curve_stable"] == (2 * genus - 2 + len(insertions) > 0), "Wrong arity flag")
        require(RationalFunction.from_json(query["claimed_value"]) == expected,
                "Changed numerical regression value")
    return {"target": target_id, "fixed_points": size, "queries": len(expected_queries),
            "symbolic_basis_metric_product_checks": "passed"}


def check_report(report):
    require(integer(report["schema_version"]) == 1 and
            report["kind"] == "gkm_localization.fixed_target_inputs" and
            report["proof_status"] == "candidate_data", "Unsupported GKM exchange or proof claim")
    require(report["source"] == json.loads((ROOT / "environments/gkm-localization-source.json").read_text()),
            "Changed producer source pin")
    require(integer(report["source"]["schema_version"]) == 1, "Unsupported producer pin schema")
    require(report["environment"] == {"sage": "10.9", "admcycles": "1.4"}, "Changed environment pin")
    require(report["coefficients"] == {
        "variables": ["x", "y"], "codimensions": [1, 1],
        "domain": "fraction field of QQ[x,y]",
        "rational_encoding": "[numerator, positive denominator]",
        "polynomial_encoding": "sorted [nonnegative exponent vector, rational coefficient]"},
        "Changed coefficient domain or encoding")
    require(list(map(integer, report["coefficients"]["codimensions"])) == [1, 1],
            "Wrong coefficient codimensions")
    require(report["cohft"] == {
        "scope": "localized classical state space and numerical integrals",
        "classes": None, "quantum_product": None, "r_matrix": None, "translation": None},
        "Unsupported CohFT-class claim")
    targets = report["targets"]
    require(len(targets) == 3, "Missing fixed surface target")
    actual_digest = hashlib.sha256(json.dumps(targets, sort_keys=True,
                                             separators=(",", ":")).encode()).hexdigest()
    require(report["targets_sha256"] == actual_digest, "GKM target digest mismatch")
    specifications = [("X0", 0, [3], [[1]]),
                      ("X1", 1, [1, 2], [[0, 1], [1, -1]]),
                      ("X2", 2, [1, 1, 1], [[0, 0, 1], [1, 0, -1], [0, 1, -1]])]
    return [check_target(frame, *spec) for frame, spec in zip(targets, specifications)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    report = json.loads(args.report.read_text(), object_pairs_hook=unique_object)
    targets = check_report(report)
    print(json.dumps({"status": "passed", "sage_required": False,
                      "scope": "GKM candidate input arithmetic; no geometric or Lean certificate claim",
                      "input_sha256": hashlib.sha256(args.report.read_bytes()).hexdigest(),
                      "targets": targets}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, TypeError, KeyError, OSError, IndexError) as error:
        print(f"GKM input checks FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
