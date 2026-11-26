#!/usr/bin/env python3
"""Compare every marked fixed locus of τ₃(E) and τ₁(E)τ₂(E) in the three classes 2E.

Run with the pinned Sage Python and --producer pointing to gkm_localisation.
The ordinary native integrals and their signed summands use the original insertions.
A separate diagnostic recovers individual vertex factors omitted by a native zero.
"""
import argparse
from collections import Counter
from dataclasses import dataclass, fields, replace
from importlib.metadata import version
from itertools import permutations
import json
from math import factorial, prod
import os
from pathlib import Path
import sys
import tempfile

from check_gkm_exceptional_genus_two import AXES, field_value
from check_gkm_inputs import unique_object
from export_gkm_inputs import ADMCYCLES_VERSION, SAGE_VERSION, producer_source, require, target_specifications
from gkm_bl2_double_exceptional_few_markings import KIND, REQUESTS
from gkm_f1_energy_two import DOUBLE_PAIRS, DOUBLE_SINGLETONS
from gkm_three_point_descendants import INPUT, read_report


# (all labeled graphs, nonzero signed graphs, single degree-two covers, parallel-edge cycles)
SHAPES = {(3,): (30, 18, 6, 4), (1, 2): (76, 46, 12, 8)}


@dataclass(frozen=True)
class GraphFactors:
    edges: tuple
    vertices: tuple
    insertion: object
    # Vertex permutations, indistinguishable parallel-edge permutations, deck groups, total.
    symmetries: tuple
    undivided: object
    signed: object


def held_cases():
    rows = {}
    for target, name, kind, requests in (
        ("X1", "f1-double-exceptional-one-marking", DOUBLE_SINGLETONS.kind, DOUBLE_SINGLETONS.requests),
        ("X1", "f1-double-exceptional-pairs", DOUBLE_PAIRS.kind, DOUBLE_PAIRS.requests),
        ("X2", "bl2-double-exceptional-few-markings", KIND, REQUESTS),
    ):
        path = INPUT.parent / f"gkm-{name}.json"
        _, grouped = read_report(path.read_bytes(), requests=requests, genus=2, kind=kind)
        for row in grouped[target]:
            key = (target, tuple(row["class"]), tuple(row["powers"]), tuple(row["labels"]))
            rows[key] = row
    return rows


def canonical_graph(locus, endpoints):
    """Minimize over ≤3 vertices, retaining genera, endpoint colors, mark numbers and multiedges."""
    vertices = tuple(locus.vertices())
    require(2 <= len(vertices) <= 3, "Unexpected number of vertices in a connected double cover")

    def signature(order):
        indices = {v: i for i, v in enumerate(order)}
        colors = tuple((endpoints.index(locus.image(v)), int(locus.genus(v)), tuple(sorted(locus.marked_points(v))))
                       for v in order)
        edges = tuple(sorted((*sorted((indices[v], indices[w])), int(locus.edge_degree(edge)))
                             for edge in locus.edges() for v, w in [locus.edge_vertices(edge)]))
        return colors, edges

    labeled = [(signature(order), order) for order in permutations(vertices)]
    graph, order = min(labeled, key=lambda entry: entry[0])
    # Every labeling yielding this minimum differs by a vertex automorphism of
    # the marked, colored multigraph. Permutations of parallel covers are separate.
    vertex_automorphisms = sum(code == graph for code, _ in labeled)
    return graph, order, vertex_automorphisms


def reference_coordinates(field, axis):
    """Express Bl₂ E₂ in F₁ coordinates by the inverse of x ↦ −x+y, y ↦ −x."""
    if axis == 0:
        return field
    x, y = field.gens()

    def normalize(value):
        q = field(value)
        return field(q.numerator()(-y, x-y)) / field(q.denominator()(-y, x-y))

    return normalize


def oriented_covers(target, endpoints, normalize):
    """Exercise both native orientations for each possible individual covering degree."""
    from gkm_localization import StableMapGKM

    result = {}
    for side in (0, 1):
        p, q = endpoints[side], endpoints[1-side]
        normal, = target.curve_normal_bundle(p, q)
        require(normal[2] == -1, "Changed normal degree on the exceptional curve")
        for degree in (1, 2):
            graph = StableMapGKM({0: {0: (0, set(), p), 1: degree}, 1: {1: (0, set(), q)}}, target)
            edge, = graph._localization_factors()["edges"]
            (adjacent, obstruction), = edge["normal_factors"]
            require(edge["fixed_points"] == (p, q) and edge["degree"] == degree and adjacent == normal[0],
                    "Native edge did not exercise the requested orientation and normal")
            result[side, degree] = tuple(map(normalize, (target.curve_weight_cohom(p, q, degree),
                                                target.curve_weight_cohom(p, adjacent), obstruction, edge["factor"])))
    return result


def source_factors(locus, insertions, raw):
    """Recover only missing individual factors, leaving the native signed summand untouched."""
    rows = {row["vertex"]: row["factor"] for row in raw["source_vertices"]}
    require(len(rows) == len(raw["source_vertices"]), "Duplicate source vertex")
    if len(rows) < len(locus.vertices()):
        # The native loop stops at a stable vertex whose local ψ degree exceeds its dimension.
        def beyond_dimension(v):
            marks = locus.marked_points(v)
            genus = locus.genus(v)
            valence = len(locus.edges(v)) + len(marks)
            return (2*genus - 2 + valence > 0 and
                    sum(insertions[i-1][0] for i in marks) > 3*genus - 3 + valence)

        blocked = {v for v in locus.vertices() if beyond_dimension(v)}
        require(raw["total"] == 0 and any(rows[v] == 0 for v in blocked if v in rows),
                "Unexplained missing source vertex")
        for v in locus.vertices():
            if v in rows:
                continue
            # Only the other dimension-zero vertices can suppress this row. Lower their ψ
            # powers while preserving all marked data at v and every other stable vertex.
            lowered = {m for u in blocked if u != v for m in locus.marked_points(u)}
            local_insertions = [(0 if i in lowered else power, divisor)
                                for i, (power, divisor) in enumerate(insertions, 1)]
            local = locus._localization_factors(local_insertions)
            recovered, = (r["factor"] for r in local["source_vertices"] if r["vertex"] == v)
            rows[v] = recovered
    require(prod(rows.values()) == raw["source_curve_factor"], "Source factors do not reassemble")
    return rows


def graph_factors(locus, target, endpoints, covers, insertions, order, vertex_automorphisms, normalize):
    raw = locus._localization_factors(insertions)
    indices = {v: i for i, v in enumerate(order)}
    edges = []
    for row in raw["edges"]:
        v, w = row["vertices"]
        degree = int(row["degree"])
        side = endpoints.index(locus.image(v))
        (_, obstruction), = row["normal_factors"]
        _, _, expected_obstruction, expected_factor = covers[side, degree]
        require(normalize(obstruction) == expected_obstruction and
                normalize(row["factor"]) == expected_factor, "Covered edge differs from native oriented sample")
        # Incidence is unoriented. The chosen source and both tangent directions can vary
        # under graph relabeling. Each orientation was checked against its own native sample.
        ends = tuple(sorted((indices[v], indices[w])))
        edges.append((ends, degree, normalize(row["factor"]), normalize(obstruction)))
    require(prod(row["factor"] for row in raw["edges"]) == raw["edge_contribution"], "Wrong edge product")

    sources = source_factors(locus, insertions, raw)
    tangent = {r["vertex"]: r for r in raw["tangent_vertices"]}
    require(set(tangent) == set(order) and len(tangent) == len(raw["tangent_vertices"]), "Missing tangent vertex")
    vertices = []
    restrictions = []
    for v in order:
        flags = tuple(sorted(map(normalize, locus.vertex_weights(v)), key=str))
        weights = tuple(sorted(map(normalize, target.tangent_space_cohom(locus.image(v))), key=str))
        require(tangent[v]["fixed_point"] == locus.image(v) and tangent[v]["valence"] == len(flags),
                "Native tangent row has the wrong endpoint or valence")
        local = tuple((int(i), int(insertions[i-1][0]), normalize(insertions[i-1][1](locus.image(v))))
                      for i in sorted(locus.marked_points(v)))
        restrictions.extend(value for _, _, value in local)
        vertices.append((flags, weights, local, normalize(tangent[v]["factor"]), normalize(sources[v])))
    require(prod(r["factor"] for r in tangent.values()) == raw["tangent_normalization"], "Wrong tangent product")
    require(prod(restrictions) == normalize(raw["insertion_factor"]), "Wrong marked insertion product")
    deck = int(prod(locus.edge_degree(e) for e in locus.edges()))
    multiplicities = Counter((ends, degree) for ends, degree, _, _ in edges)
    parallel = prod(factorial(m) for m in multiplicities.values())
    total = vertex_automorphisms * parallel * deck
    require(parallel == locus._parallel_edge_permutation_count() and
            total == locus.automorphism_group_size() == raw["automorphism_denominator"],
            "Changed vertex, parallel-edge, or deck contribution to the symmetry denominator")
    undivided = prod(raw[k] for k in ("edge_contribution", "tangent_normalization", "insertion_factor",
                                     "source_curve_factor"))
    require(undivided == raw["total_before_automorphisms"] and undivided / total == raw["total"] ==
            locus.localization_contribution(insertions),
            "Signed summand does not reassemble")
    return GraphFactors(tuple(sorted(edges)), tuple(vertices), normalize(raw["insertion_factor"]),
                        (vertex_automorphisms, parallel, deck, total), normalize(undivided), normalize(raw["total"]))


def native_frame(target, frame, spec, axis, ring, field, cases):
    from sage.all import ZZ
    from gkm_localization import StableMapsGKM

    normalize = reference_coordinates(field, axis)
    ray = spec["exceptional"][axis]
    primitive = tuple(spec["curves"][(ray,)])
    beta = 2*(ZZ**len(primitive))(primitive)
    pinned, = (e for e in frame["edges"] if e["class"] == list(primitive))
    points = tuple(tuple(p) for p in frame["points"])
    endpoints = tuple(points[pinned[k]] for k in ("source", "target"))
    require(list(points) == sorted(target.fixed_points()) and target.curve_class(*endpoints)*2 == beta and
            pinned["wall"] == [ray], "Changed exceptional edge, coordinates or orientation")
    label = f"E{axis+1}"
    column = frame["basis"].index(label)
    divisor = target.cohomology_class({p: ring(field_value(field, row[column]))
                                       for p, row in zip(points, frame["basis_to_fixedpoint"])})
    require({p for p in points if divisor(p)} == set(endpoints), "Changed support of the marked divisor")
    covers = oriented_covers(target, endpoints, normalize)
    maps = StableMapsGKM(target)
    result = {}
    for powers, shape in SHAPES.items():
        insertions = [(power, divisor) for power in powers]
        rows = {}
        for locus in maps.fixed_loci(2, len(powers), beta):
            require(locus.genus() == 2 and locus.degree() == beta, "Wrong genus or full curve class")
            signature, order, vertex_automorphisms = canonical_graph(locus, endpoints)
            require(signature not in rows, "Duplicate fully decorated native graph")
            rows[signature] = graph_factors(locus, target, endpoints, covers, insertions, order,
                                            vertex_automorphisms, normalize)
        topology = (len(rows), sum(r.signed != 0 for r in rows.values()),
                    sum(len(edges) == 1 and edges[0][2] == 2 for _, edges in rows),
                    sum(len(edges) == len(vertices) for vertices, edges in rows))
        require(topology == shape, f"Changed coverage on {spec['id']}/{label}, powers {powers}: {topology}")
        held = cases[spec["id"], tuple(beta), powers, (label,)*len(powers)]
        native = field(maps.integrate(2, len(powers), beta, insertions))
        require(sum(r.signed for r in rows.values()) == normalize(native) and
                native == field_value(field, held["equivariant"]) == field(held["ordinary"][0])/held["ordinary"][1],
                "Native integral, held full-field receipt and signed graph sum differ")
        result[powers] = rows
        print(f"{spec['id']}/{label}, powers {powers}: {len(rows)} graphs, {topology[1]} nonzero, sum {native}",
              flush=True)
    return covers, result


def compare_rows(reference, incoming):
    require(reference.keys() == incoming.keys(), "Different decorated graphs or marked signatures")
    for signature, row in reference.items():
        for member in fields(row):
            require(getattr(row, member.name) == getattr(incoming[signature], member.name),
                    f"Changed {member.name} on graph {signature}")


def symmetry_control(rows):
    # Exchange vertex and parallel-edge symmetry on a cycle. The full order and every
    # rational value remain the same, so a check of totals alone would accept this error.
    key = next(k for k, row in rows.items() if row.symmetries == (1, 2, 1, 2))
    tampered = dict(rows)
    tampered[key] = replace(rows[key], symmetries=(2, 1, 1, 2))
    try:
        compare_rows(rows, tampered)
    except ValueError as exc:
        require("Changed symmetries" in str(exc), "Symmetry control failed for an unrelated reason")
        return
    raise ValueError("Accepted an incorrect parallel-edge symmetry with the correct total order")


def check(producer, pin):
    from sage.all import Fan, LaurentPolynomialRing, PolynomialRing, QQ, ZZ
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
    data = json.loads(INPUT.read_bytes(), object_pairs_hook=unique_object)
    require(data["source"] == pin, "Changed provenance of pinned target inputs")
    frames = {f["target"]: f for f in data["targets"]}
    specs = {s["id"]: s for s in target_specifications()}
    ring = LaurentPolynomialRing(ZZ, names=("x", "y"))
    field = PolynomialRing(QQ, names=("x", "y")).fraction_field()
    cases = held_cases()
    comparisons = []
    for name, axis, _ in AXES:
        spec = specs[name]
        target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), ring,
                                       curve_basis=spec["curves"], name=name)
        comparisons.append(native_frame(target, frames[name], spec, axis, ring, field, cases))
    reference_covers, reference_rows = comparisons[0]
    for covers, records in comparisons[1:]:
        require(covers == reference_covers, "Different oriented cover factors after character change")
        for powers in SHAPES:
            compare_rows(reference_rows[powers], records[powers])
    symmetry_control(reference_rows[(1, 2)])
    print("Matched all 106 decorated graph signatures on both axes and rejected a changed symmetry decomposition.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    producer, pin = producer_source(parser.parse_args().producer)
    with tempfile.TemporaryDirectory(prefix="gw-double-exceptional-") as directory:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            path = Path(directory) / variable
            path.mkdir()
            os.environ[variable] = str(path)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        check(producer, pin)
