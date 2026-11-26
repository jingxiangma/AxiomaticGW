#!/usr/bin/env python3
"""Export exact GKM state-space and query inputs for the three fixed surfaces.

Use the pinned Sage Python with --producer pointing to the gkm_localisation
checkout (or its gkm_localization package directory). Producer source hashes
are checked before import. All caches are isolated and online admcycles
lookup is disabled. This exports candidate data, not CohFT classes or Lean
proofs. Known numerical answers belong in the separate regression checker.
"""

import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PIN = ROOT / "environments" / "gkm-localization-source.json"
SAGE_VERSION = "10.9"
ADMCYCLES_VERSION = "1.4"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def producer_source(path):
    path = path.resolve()
    if path.name == "gkm_localization" and (path / "__init__.py").is_file():
        path = path.parent
    pin = json.loads(PIN.read_text())
    revision = subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    require(revision == pin["revision"], "Producer revision differs from the audited pin")
    for name, expected in pin["python_sources"].items():
        require(hashlib.sha256((path / name).read_bytes()).hexdigest() == expected,
                f"Producer source differs from the audited pin: {name}")
    return path, pin


def target_specifications():
    """Toric presentations with the goal's full effective-class coordinates.

    Ray 3 is E1 and ray 4 is E2. Hyperplane and point lifts are explicit
    sums/products of toric divisor restrictions. Geometric identification
    with the surfaces remains a named comparison obligation.
    """
    return [
        {"id": "X0", "rays": [(1, 0), (0, 1), (-1, -1)],
         "cones": [(0, 1), (1, 2), (2, 0)],
         "curves": {(0,): (1,), (1,): (1,), (2,): (1,)},
         "exceptional": [], "hyperplane": [2], "generators": [0]},
        {"id": "X1", "rays": [(1, 0), (0, 1), (-1, -1), (1, 1)],
         "cones": [(0, 3), (3, 1), (1, 2), (2, 0)],
         "curves": {(0,): (0, 1), (1,): (0, 1), (2,): (1, 1), (3,): (1, 0)},
         "exceptional": [3], "hyperplane": [2], "generators": [3, 0]},
        {"id": "X2", "rays": [(1, 0), (0, 1), (-1, -1), (1, 1), (-1, 0)],
         "cones": [(0, 3), (3, 1), (1, 4), (4, 2), (2, 0)],
         "curves": {(0,): (0, 1, 1), (1,): (0, 0, 1), (2,): (1, 0, 1),
                    (3,): (1, 0, 0), (4,): (0, 1, 0)},
         "exceptional": [3, 4], "hyperplane": [0, 3], "generators": [3, 4, 1]},
    ]


def export_inputs(producer, pin):
    # Imports follow cache isolation. Preloading sage.all also supports the
    # producer's import convention without using its historical Sage launcher.
    from sage.all import (Fan, LaurentPolynomialRing, PolynomialRing, QQ, ZZ,
                          diagonal_matrix, matrix, prod, vector)
    from sage.version import version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default

    require(version == SAGE_VERSION, "Sage differs from the audited environment")
    require(importlib.metadata.version("admcycles") == ADMCYCLES_VERSION,
            "admcycles differs from the audited environment")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapsGKM, toric_target_from_fan

    require(Path(gkm_localization.__file__).resolve().parent ==
            producer / "gkm_localization", "Imported a different producer package")
    R = LaurentPolynomialRing(ZZ, names=("x", "y"))
    polynomial_ring = PolynomialRing(QQ, names=("x", "y"))
    K = polynomial_ring.fraction_field()

    def rational(value):
        value = QQ(value)
        return [int(value.numerator()), int(value.denominator())]

    def polynomial(value):
        value = polynomial_ring(value)
        return [[list(map(int, powers)), rational(coefficient)]
                for powers, coefficient in sorted(value.dict().items())]

    def fraction(value):
        value = K(value)
        denominator = polynomial(value.denominator())
        require(bool(denominator), "Zero polynomial denominator")
        return {"numerator": polynomial(value.numerator()), "denominator": denominator,
                "denominator_nonzero_term": denominator[0]}

    def encoded_matrix(value):
        return [[fraction(coefficient) for coefficient in row] for row in value.rows()]

    def ordinary(value):
        value = K(value)
        denominator = value.denominator()(0, 0)
        require(denominator != 0, "Unresolved pole in ordinary specialization")
        return QQ(value.numerator()(0, 0) / denominator)

    def character(value):
        value = polynomial_ring(value)
        coefficients = [value.monomial_coefficient(x) for x in polynomial_ring.gens()]
        require(value == sum(c * x for c, x in zip(coefficients, polynomial_ring.gens()))
                and all(c in ZZ for c in coefficients), "Nonintegral or nonlinear character")
        return list(map(int, coefficients))

    frames = []
    for specification in target_specifications():
        target_id = specification["id"]
        print(f"Exporting {target_id}", file=sys.stderr, flush=True)
        rays = specification["rays"]
        X = toric_target_from_fan(
            Fan(cones=specification["cones"], rays=rays), R,
            curve_basis=specification["curves"], name=target_id)
        points = sorted(X.fixed_points())
        point_index = {p: i for i, p in enumerate(points)}
        euler = [K(prod(X.tangent_space_cohom(p))) for p in points]
        require(all(e != 0 for e in euler), "Zero tangent Euler factor")

        divisors = []
        for rho in range(len(rays)):
            restrictions = {}
            for p in points:
                if rho in p:
                    dual = matrix([rays[j] for j in p]).transpose().inverse()
                    row = dual.rows()[p.index(rho)]
                    restrictions[p] = sum(row[j] * R.gen(j) for j in range(2))
                else:
                    restrictions[p] = R.zero()
            divisors.append(X.cohomology_class(restrictions))
        unit = X.cohomology_class({p: R.one() for p in points})
        hyperplane = X.cohomology_class({
            p: sum(divisors[j](p) for j in specification["hyperplane"]) for p in points})
        point = X.cohomology_class({p: divisors[0](p) * divisors[2](p) for p in points})
        basis = [unit, hyperplane] + [divisors[j] for j in specification["exceptional"]] + [point]
        names = ["unit", "H"] + [f"E{i+1}" for i in range(len(specification["exceptional"]))] + ["pt"]
        B = matrix(K, [[f(p) for f in basis] for p in points])
        require(B.det() != 0, "Singular basis restriction matrix")
        inverse = B.inverse()
        metric = B.transpose() * diagonal_matrix(K, [1 / e for e in euler]) * B
        inverse_metric = inverse * diagonal_matrix(K, euler) * inverse.transpose()
        require(B * inverse == matrix.identity(K, len(points)) and
                inverse * B == matrix.identity(K, len(points)), "Failed basis inverse")
        require(metric * inverse_metric == matrix.identity(K, len(points)) and
                inverse_metric * metric == matrix.identity(K, len(points)), "Failed metric inverse")
        products = [[inverse * vector(K, [f(p) * h(p) for p in points])
                     for h in basis] for f in basis]
        c1_restrictions = [sum(X.tangent_space_cohom(p)) for p in points]
        c1_coordinates = inverse * vector(K, c1_restrictions)

        intersections = [[QQ(sum(K(D(p) * divisors[rho](p)) / e
                                  for p, e in zip(points, euler)))
                          for rho in range(len(rays))] for D in basis[1:-1]]
        curve_map = [[intersections[0][rho] for rho in specification["generators"]]]
        curve_map += [[-row[rho] for rho in specification["generators"]]
                      for row in intersections[1:]]
        energy = [QQ(sum(K(c * divisors[rho](p)) / e
                         for p, e, c in zip(points, euler, c1_restrictions)))
                  for rho in specification["generators"]]
        require(all(e in ZZ and e > 0 for e in energy), "Nonpositive or nonintegral energy")
        require(all(c in ZZ for row in curve_map for c in row), "Nonintegral curve transport")

        edges = []
        for p, q in sorted(X.fixed_curves()):
            wall = tuple(sorted(set(p).intersection(q)))
            weight = character(X.curve_weight_cohom(p, q))
            require(character(X.curve_weight_cohom(q, p)) == [-c for c in weight],
                    "Opposite edge weights disagree")
            edges.append({"source": point_index[p], "target": point_index[q],
                          "weight": weight, "class": list(map(int, X.curve_class(p, q))),
                          "wall": list(map(int, wall)), "normal_bundles": [
                              [point_index[u], point_index[v], int(degree)]
                              for u, v, degree in X.curve_normal_bundle(p, q)]})

        rank = len(specification["generators"])
        zero = [0] * rank
        requests = [(1, zero, [(0, 1)]), (2, zero, [(1, 1)])]
        if target_id == "X0":
            requests.append((0, [1], [(0, len(basis)-1)] * 2))
        elif target_id == "X1":
            requests.append((0, [0, 1], [(0, len(basis)-1)]))
        else:
            requests.append((0, [1, 0, 0], []))
        queries = []
        maps = StableMapsGKM(X)
        for genus, beta, insertions in requests:
            value = maps.integrate(genus, len(insertions), (ZZ ** rank)(beta),
                                   [(power, basis[index]) for power, index in insertions])
            queries.append({"genus": genus, "class": beta, "insertions": [
                {"label": i, "psi": power, "basis": index}
                for i, (power, index) in enumerate(insertions)],
                "curve_stable": 2 * genus - 2 + len(insertions) > 0,
                "claimed_value": fraction(value)})

        frames.append({
            "target": target_id, "rays": [list(ray) for ray in rays],
            "points": [list(map(int, p)) for p in points], "edges": edges, "basis": names,
            "tangent_characters": [[character(w) for w in X.tangent_space_cohom(p)] for p in points],
            "euler": [fraction(e) for e in euler],
            "basis_to_fixedpoint": encoded_matrix(B), "fixedpoint_to_basis": encoded_matrix(inverse),
            "metric": encoded_matrix(metric), "inverse_metric": encoded_matrix(inverse_metric),
            "products": [[[fraction(c) for c in coefficients] for coefficients in row] for row in products],
            "c1_coordinates": [fraction(c) for c in c1_coordinates],
            "curve_to_signed_lattice": [list(map(int, row)) for row in curve_map],
            "energy_weights": list(map(int, energy)),
            "divisor_curve_intersections": [[rational(c) for c in row] for row in intersections],
            "ordinary_metric": [[rational(ordinary(c)) for c in row] for row in metric.rows()],
            "ordinary_products": [[[rational(ordinary(c)) for c in coefficients]
                                   for coefficients in row] for row in products],
            "queries": queries,
        })
    return {"schema_version": 1, "kind": "gkm_localization.fixed_target_inputs",
            "proof_status": "candidate_data", "source": pin,
            "environment": {"sage": version, "admcycles": ADMCYCLES_VERSION},
            "coefficients": {"variables": ["x", "y"], "codimensions": [1, 1],
                             "domain": "fraction field of QQ[x,y]",
                             "rational_encoding": "[numerator, positive denominator]",
                             "polynomial_encoding": "sorted [nonnegative exponent vector, rational coefficient]"},
            "cohft": {"scope": "localized classical state space and numerical integrals",
                      "classes": None, "quantum_product": None, "r_matrix": None, "translation": None},
            "targets_sha256": digest(frames), "targets": frames}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    args = parser.parse_args()
    producer, pin = producer_source(args.producer)
    sys.dont_write_bytecode = True
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-gkm-export-") as temporary:
        for key, leaf in [("DOT_SAGE", "sage"), ("ADMCYCLES_CACHE_DIR", "admcycles"),
                          ("MPLCONFIGDIR", "matplotlib"), ("XDG_CACHE_HOME", "xdg")]:
            location = Path(temporary) / leaf
            location.mkdir()
            os.environ[key] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        report = export_inputs(producer, pin)
        print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"GKM input export FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
