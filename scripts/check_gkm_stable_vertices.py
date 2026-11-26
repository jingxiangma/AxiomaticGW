#!/usr/bin/env python3
"""Check surface multiple-cover edges and stable source vertices against the pinned GKM producer."""

import argparse
from collections import Counter
from importlib.metadata import version
from math import factorial
import os
from pathlib import Path
import sys
import tempfile

from export_gkm_inputs import (
    ADMCYCLES_VERSION, SAGE_VERSION, producer_source, require, target_specifications,
)


def check_edges(target):
    from sage.all import prod
    from gkm_localization import StableMapGKM

    def oriented(source, destination, degree):
        tangent = target.curve_weight_cohom(source, destination) / degree
        (source_branch, target_branch, normal_degree), = target.curve_normal_bundle(source, destination)
        normal = target.curve_weight_cohom(source, source_branch)
        k = degree * normal_degree
        require(target.curve_weight_cohom(destination, target_branch) == normal - k * tangent,
                "Wrong terminal normal character")
        if k >= 0:
            b = 1 / prod(normal - j * tangent for j in range(k + 1))
        else:
            b = prod(normal + j * tangent for j in range(1, -k))
        return (-1)**degree * b / (factorial(degree)**2 * tangent**(2 * degree))

    curves = target.fixed_curves()
    for p, q in curves:
        for degree in (1, 2, 3):
            graph = StableMapGKM({0: {0: (0, set(), p), 1: degree}, 1: {1: (0, set(), q)}}, target)
            require(graph.degree() == degree * target.curve_class(p, q), "Changed multiple-cover class")
            edge, = graph._localization_factors([])["edges"]
            require(edge["degree"] == degree and set(edge["fixed_points"]) == {p, q}, "Changed edge data")
            require(edge["factor"] == oriented(p, q, degree) == oriented(q, p, degree),
                    "Surface edge factor disagrees with the two oriented evaluations")
    return 3 * len(curves)


def check_target(target, ring):
    from sage.all import prod
    from gkm_localization import StableMapGKM

    center = min(target.fixed_points())
    neighbors = sorted(q for _, q in target.fixed_curves(center))
    tangents = [target.curve_weight_cohom(center, q) for q in neighbors]
    require(len(tangents) == 2, "Expected two tangent directions on the selected surface")
    unit = target.cohomology_class({p: ring.one() for p in target.fixed_points()})
    # Each branch is (tangent direction, covering degree). Mixed flags have unequal characters.
    rational = [
        ([(0, 1), (1, 2), (0, 1)], ()),
        ([(0, 1), (1, 2), (0, 2), (1, 1)], ()),
        ([(0, 1), (1, 2), (0, 2)], (0, 1)),
        ([(0, 1), (1, 2)], (2, 0, 0, 0)),
        ([(0, 1), (1, 2)], (3,)),
    ]
    elliptic = [([(0, 1)], ()), ([(1, 2)], ()), ([(0, 1)], (3,))]

    for genus, cases in ((0, rational), (1, elliptic)):
        for branches, marked in cases:
            graph_data = {0: {0: (genus, set(range(1, len(marked) + 1)), center)}}
            expected_degree = 0
            flags = []
            for i, (direction, cover) in enumerate(branches, start=1):
                q = neighbors[direction]
                graph_data[0][i] = cover
                graph_data[i] = {i: (0, set(), q)}
                flags.append(tangents[direction] / cover)
                expected_degree += cover * target.curve_class(center, q)
            graph = StableMapGKM(graph_data, target)
            require(graph.degree() == expected_degree, "Changed full graph class")
            center_vertex, = (v for v in graph.vertices() if graph.image(v) == center)
            require(Counter(graph.vertex_weights(center_vertex)) == Counter(flags),
                    "Changed characters of the incident flags")
            factors = graph._localization_factors([(d, unit) for d in marked])
            row, = (r for r in factors["source_vertices"] if r["vertex"] == center_vertex)
            dimension = 3 * genus - 3 + len(marked) + len(flags)
            remaining = dimension - sum(marked)
            if remaining < 0:
                expected = 0
            elif genus == 0:
                expected = factorial(dimension) * sum(1 / w for w in flags)**remaining / (
                    factorial(remaining) * prod(factorial(d) for d in marked) *
                    prod(flags) * prod(tangents)
                )
            else:
                w, = flags
                expected = 1 / (24 * w**2) - sum(1 / u for u in tangents) / (24 * w)
            require(row["factor"] == expected,
                    f"Native genus-{genus} center disagrees for covers {branches}, marks {marked}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    producer, _ = producer_source(parser.parse_args().producer)
    with tempfile.TemporaryDirectory(prefix="gw-stable-vertices-") as directory:
        for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            location = Path(directory) / name
            location.mkdir()
            os.environ[name] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        from sage.all import Fan, LaurentPolynomialRing, ZZ
        from sage.version import version as sage_version
        from admcycles.admcycles import set_online_lookup, set_online_lookup_default

        require(sage_version == SAGE_VERSION and version("admcycles") == ADMCYCLES_VERSION,
                "The Sage/admcycles environment differs from the audited versions")
        set_online_lookup(False)
        set_online_lookup_default(False)
        sys.path.insert(0, str(producer))
        import gkm_localization
        from gkm_localization import toric_target_from_fan

        require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
                "Imported a different producer checkout")
        ring = LaurentPolynomialRing(ZZ, names=("x", "y"))
        for spec in target_specifications():
            target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), ring,
                                           curve_basis=spec["curves"], name=spec["id"])
            count = check_edges(target)
            check_target(target, ring)
            print(f"{spec['id']}: {count} multiple-cover edges, five rational and three elliptic vertices agree.")


if __name__ == "__main__":
    main()
