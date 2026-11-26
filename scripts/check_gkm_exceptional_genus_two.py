#!/usr/bin/env python3
"""Check the six native genus-two cubic-descendant loci on each primitive exceptional axis."""
import argparse
from importlib.metadata import version
import json
import os
from pathlib import Path
import sys
import tempfile

from check_gkm_inputs import polynomial, unique_object
from export_gkm_inputs import ADMCYCLES_VERSION, SAGE_VERSION, producer_source, require, target_specifications
from gkm_three_point_descendants import INPUT, TARGETS, read_report


AXES = (("X1", 0, "f1"), ("X2", 0, "bl2"), ("X2", 1, "bl2-second"))


def field_value(field, encoded):
    x, y = field.gens()

    def value(terms):
        return sum((field(c) * x**i * y**j for (i, j), c in polynomial(terms).items()), field.zero())

    return value(encoded["numerator"]) / value(encoded["denominator"])


def source_factor(genus, marked, w, t):
    """One flag of weight w and transverse character t, with ψ³ at the marked end."""
    if genus == 0:
        return ((-w)**3 if marked else w) / (w*t)
    if genus == 1:
        # The marked vertex exceeds dim Mbar_1,2. At the unmarked vertex the ψ and
        # tangent-direction λ terms cancel, leaving the transverse λ term.
        return 0 if marked else -1/(24*w*t)
    if marked:
        return -11/(2880*w) + 7/(5760*t)
    return 1/(1152*t*w**2)


def check_locus(target, locus, beta, endpoints, weights, divisor):
    from sage.all import prod

    edge, = locus.edges()
    vertices = tuple(locus.edge_vertices(edge))
    images = tuple(locus.image(v) for v in vertices)
    at_point = dict(zip(images, vertices))
    require(set(images) == set(endpoints) and set(vertices) == set(locus.vertices()) and
            locus.degree() == beta and locus.edge_degree(edge) == locus.automorphism_group_size() == 1,
            "Changed decorated exceptional edge, degree or automorphism order")
    marked = locus.marked_point_to_vertex(1)
    require(locus.marked_points() == 1 and marked in vertices and
            locus.marked_point_image(1) == locus.image(marked), "Changed marked flag")
    genera = {v: int(locus.genus(v)) for v in vertices}
    require(set(genera.values()) <= {0, 1, 2} and sum(genera.values()) == 2, "Changed genus split")

    insertions = [(3, divisor)]
    factors = locus._localization_factors(insertions)
    edge_data, = factors["edges"]
    p, q = images
    w, _ = weights[p]
    normal, = target.curve_normal_bundle(p, q)
    require(edge_data["edge"] == edge and tuple(edge_data["vertices"]) == vertices and
            tuple(edge_data["fixed_points"]) == images and edge_data["degree"] == 1 and
            normal[2] == -1 and edge_data["normal_factors"] == ((normal[0], 1),) and
            edge_data["factor"] == factors["edge_contribution"] == -1/w**2,
            "Changed signed degree-one edge or its normal factor")

    tangent_rows = {row["vertex"]: row for row in factors["tangent_vertices"]}
    require(len(factors["tangent_vertices"]) == len(tangent_rows) == 2, "Missing tangent vertex")
    source_rows = {row["vertex"]: row for row in factors["source_vertices"]}
    require(len(source_rows) == len(factors["source_vertices"]) and
            set(source_rows) <= set(vertices), "Duplicate or unknown source vertex")
    expected_sources = []
    for v, p in zip(vertices, images):
        w, t = weights[p]
        row = tangent_rows[v]
        require(tuple(locus.vertex_weights(v)) == (w,) and row["fixed_point"] == p and
                row["valence"] == 1 and row["factor"] == w*t, "Changed flag or vertex Euler factor")
        expected = source_factor(genera[v], v == marked, w, t)
        if v in source_rows:
            require(source_rows[v]["factor"] == expected, "Changed Hodge or unstable vertex factor")
        else:
            # The native loop stops at the marked elliptic zero. On the same fixed locus
            # a primary insertion exposes the other vertex, whose data are independent of ψ³.
            require(v != marked and genera[marked] == 1 and source_rows[marked]["factor"] == 0,
                    "Unexplained missing source vertex")
            primary = locus._localization_factors([(0, divisor)])
            unmarked, = (r for r in primary["source_vertices"] if r["vertex"] == v)
            require(unmarked["factor"] == expected, "Changed unmarked elliptic Hodge factor")
        expected_sources.append(expected)

    euler = prod(w*t for w, t in weights.values())
    insertion = weights[locus.image(marked)][1]
    source = prod(expected_sources)
    expected = (-1 / weights[images[0]][0]**2) * euler * insertion * source
    require(factors["tangent_normalization"] == euler and factors["insertion_factor"] == insertion and
            factors["source_curve_factor"] == source and factors["automorphism_denominator"] == 1,
            "Changed tangent product, marked restriction, source product or automorphism factor")
    require(factors["total_before_automorphisms"] == factors["total"] == expected ==
            locus.localization_contribution(insertions), "Changed individual localization contribution")
    signature = (genera[at_point[endpoints[0]]], endpoints.index(locus.image(marked)))
    return signature, expected


def check_covers(target, beta, endpoints, weights):
    """Compare native edge factors for both orientations before dividing out the cover group."""
    from math import factorial
    from sage.all import prod
    from gkm_localization import StableMapGKM

    for degree in range(1, 7):
        for p, q in (endpoints, endpoints[::-1]):
            graph = StableMapGKM({0: {0: (0, set(), p), 1: degree}, 1: {1: (0, set(), q)}}, target)
            require(graph.degree() == degree * beta, "Wrong covered exceptional class")
            factors = graph._localization_factors()
            row, = factors["edges"]
            require(tuple(row["fixed_points"]) == (p, q) and row["degree"] == degree,
                    "The native graph did not exercise the requested orientation and degree")
            w, n = weights[p]
            flag = w / degree
            obstruction = prod(n + j * flag for j in range(1, degree))
            expected = (-1)**degree * obstruction / (factorial(degree)**2 * flag**(2*degree))
            normal, = target.curve_normal_bundle(p, q)
            require(row["normal_factors"] == ((normal[0], obstruction),),
                    f"Cover {degree} at {p}: normal factor {row['normal_factors']} differs from {obstruction}")
            require(row["factor"] == factors["edge_contribution"] == expected,
                    f"Cover {degree} at {p}: edge factor {row['factor']} differs from {expected}")
            require(factors["automorphism_denominator"] == degree,
                    f"Cover {degree} at {p}: changed deck group {factors['automorphism_denominator']}")
            euler = prod(t * normal_weight for t, normal_weight in weights.values())
            require(factors["tangent_normalization"] == euler and
                    factors["source_curve_factor"] == -flag**2 / euler and
                    factors["total"] == -flag**2 * expected / degree,
                    f"Cover {degree} at {p}: changed unstable endpoints or full graph contribution")


def check_chain(target, beta, endpoints, weights, divisor):
    """Check the marked bivalent genus-two center and the symmetry of its two rational leaves."""
    from gkm_localization import StableMapGKM

    p, q = endpoints
    graph = StableMapGKM({0: {0: (0, set(), p), 1: 1}, 1: {1: (2, {1}, q), 2: 1},
                          2: {2: (0, set(), p)}}, target)
    factors = graph._localization_factors([(3, divisor)])
    marked = graph.marked_point_to_vertex(1)
    row, = (v for v in factors["source_vertices"] if v["vertex"] == marked)
    w, t = weights[q]
    center = 11*t/(720*w**4) - 103/(2880*w**3) + 3/(320*t*w**2)
    require(graph.degree() == 2*beta and graph.image(marked) == q and
            tuple(row["incident_edge_weights"]) == (w, w) and set(row["target_weights"]) == {w, t} and
            tuple(row["descendent_powers"]) == (3,) and row["genus"] == 2 and row["factor"] == center,
            "Changed ordered double exceptional bivalent source vertex")
    require(factors["insertion_factor"] == t and factors["automorphism_denominator"] == 2 and
            factors["total"] == t**3 * center / 2, "Changed complete signed bivalent graph")


def check_axis(target, spec, frame, axis, report_name, ring):
    from sage.all import QQ, ZZ, matrix
    from gkm_localization import StableMapsGKM

    field = ring.change_ring(QQ).fraction_field()
    x, y = field.gens()
    ray = spec["exceptional"][axis]
    label = f"E{axis+1}"
    coordinates = tuple(spec["curves"][(ray,)])
    require(coordinates == tuple(int(i == axis) for i in range(len(spec["exceptional"]) + 1)),
            "Exceptional wall is not the requested primitive curve coordinate")
    beta = (ZZ**len(coordinates))(coordinates)
    points = [tuple(p) for p in frame["points"]]
    require(points == sorted(target.fixed_points()), "Changed pinned fixed-point indexing")
    pinned_edge, = (e for e in frame["edges"] if e["class"] == list(coordinates))
    endpoints = tuple(points[pinned_edge[key]] for key in ("source", "target"))
    require(pinned_edge["wall"] == [ray] and set(endpoints) == {p for p in points if ray in p} and
            target.curve_class(*endpoints) == beta, "Changed exceptional edge or endpoints")

    restrictions = {}
    for i, p in enumerate(points):
        # The own toric divisor is the dual character of the exceptional ray on each cone.
        if ray in p:
            dual = matrix(ZZ, [spec["rays"][j] for j in p]).transpose().inverse()
            restrictions[p] = sum(c * u for c, u in zip(dual.rows()[p.index(ray)], ring.gens()))
        else:
            restrictions[p] = ring.zero()
        held = frame["basis_to_fixedpoint"][i][frame["basis"].index(label)]
        require(restrictions[p] == field_value(field, held), "Changed own-divisor restriction")

    weights = {}
    for p, q in (endpoints, endpoints[::-1]):
        t = field(restrictions[p])
        # For O(-1), the transverse character at the opposite end is t + w.
        w = field(restrictions[q]) - t
        i = points.index(p)
        pinned_tangents = {a*x + b*y for a, b in frame["tangent_characters"][i]}
        require(w == target.curve_weight_cohom(p, q) and
                {w, t} == pinned_tangents == set(target.tangent_space_cohom(p)) and
                w*t == field_value(field, frame["euler"][i]), "Changed tangent or transverse weight")
        weights[p] = w, t

    p, q = endpoints
    a, b = pinned_edge["weight"]
    normal, = pinned_edge["normal_bundles"]
    require(weights[p][0] == a*x + b*y and normal[2] == -1 and
            tuple(target.curve_normal_bundle(p, q)) == ((points[normal[0]], points[normal[1]], -1),),
            "Changed oriented exceptional weight or normal bundle endpoints")

    check_covers(target, beta, endpoints, weights)
    divisor = target.cohomology_class(restrictions)
    check_chain(target, beta, endpoints, weights, divisor)
    maps = StableMapsGKM(target)
    loci = maps.fixed_loci(2, 1, beta)
    seen, total = set(), field.zero()
    for locus in loci:
        signature, contribution = check_locus(target, locus, beta, endpoints, weights, divisor)
        seen.add(signature)
        total += contribution
    require(len(loci) == 6 and seen == {(g, m) for g in range(3) for m in range(2)},
            "Expected all six genus splits and marked-end assignments")
    transverse_sum = sum(t for w, t in weights.values()) / 240
    expected = (x+y)/240 if axis == 0 else (y-2*x)/240
    require(total == transverse_sum == expected == maps.integrate(2, 1, beta, [(3, divisor)]),
            "Changed full equivariant localization sum")

    requests = {t: [] for t, _, _ in TARGETS}
    requests[spec["id"]] = [(coordinates, (3,), (label,))]
    path = INPUT.parent / f"gkm-research-{report_name}-exceptional-cubic.json"
    _, grouped = read_report(path.read_bytes(), requests=requests, genus=2,
                             kind="gkm_localization.surface_research_query")
    case, = grouped[spec["id"]]
    require(field_value(field, case["equivariant"]) == total and case["ordinary"] == [0, 1],
            "Held equivariant field or ordinary specialization disagrees with the locus sum")
    print(f"{spec['id']}/{label}: twelve oriented covers, the double-class chain, "
          f"six primitive loci and twelve vertex factors agree; "
          f"240 * field = {ring(240*total)}, ordinary = 0.")


def check(producer, pin):
    from sage.all import Fan, LaurentPolynomialRing, ZZ
    from sage.version import version as sage_version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default

    require(sage_version == SAGE_VERSION and version("admcycles") == ADMCYCLES_VERSION, "Changed environment")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import toric_target_from_fan

    require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
            "Imported a different GKM checkout")
    inputs = json.loads(INPUT.read_bytes(), object_pairs_hook=unique_object)
    require(inputs["source"] == pin, "Different producer in held target inputs")
    frames = {f["target"]: f for f in inputs["targets"]}
    specs = {s["id"]: s for s in target_specifications()}
    ring = LaurentPolynomialRing(ZZ, names=("x", "y"))
    for name, axis, report_name in AXES:
        spec = specs[name]
        target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), ring,
                                       curve_basis=spec["curves"], name=name)
        check_axis(target, spec, frames[name], axis, report_name, ring)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    producer, pin = producer_source(parser.parse_args().producer)
    with tempfile.TemporaryDirectory(prefix="gw-genus-two-cubic-") as directory:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            path = Path(directory) / variable
            path.mkdir()
            os.environ[variable] = str(path)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        check(producer, pin)
