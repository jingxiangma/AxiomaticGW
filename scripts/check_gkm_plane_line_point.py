#!/usr/bin/env python3
"""Check the individual native localization flags of a point-marked plane line."""
import argparse
from importlib.metadata import version
import os
from pathlib import Path
import sys
import tempfile

from export_gkm_inputs import producer_source, require, target_specifications


def check(producer):
    from sage.all import Fan, LaurentPolynomialRing, ZZ, prod
    from sage.version import version as sage_version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default

    require(sage_version == "10.9" and version("admcycles") == "1.4", "Changed environment")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapsGKM, toric_target_from_fan

    require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
            "Imported a different GKM producer")
    spec = next(s for s in target_specifications() if s["id"] == "X0")
    ring = LaurentPolynomialRing(ZZ, names=("x", "y"))
    field = ring.fraction_field()
    x, y = map(field, ring.gens())
    target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), ring,
                                   curve_basis=spec["curves"], name="X0")
    points = sorted(target.fixed_points())
    marked = points[1]
    euler = prod(target.tangent_space_cohom(marked))
    require(field(euler) == (x-y)*(-y), "Changed point restriction")
    point = target.cohomology_class({p: euler if p == marked else ring.zero() for p in points})
    beta = (ZZ**1)((1,))
    maps = StableMapsGKM(target)
    loci = maps.fixed_loci(0, 1, beta)
    require(len(loci) == 6, "Expected two marked ends on each of three lines")
    directions = set()
    for locus in loci:
        edge, = locus.edges()
        require(locus.edge_degree(edge) == 1 and locus.automorphism_group_size() == 1,
                "Unexpected covering or automorphism")
        if locus.marked_point_image(1) == marked:
            v, = locus.vertices(mapping_to=marked)
            direction, = locus.vertex_weights(v)
            directions.add(field(direction))
    require(directions == {x-y, -y}, "Changed marked tangent characters")
    for k in (0, 1, 2, 3, 6):
        insertion = [(k, point)]
        total = field.zero()
        for locus in loci:
            term = field(locus.localization_contribution(insertion))
            if locus.marked_point_image(1) == marked:
                vertex, = locus.vertices(mapping_to=marked)
                direction, = map(field, locus.vertex_weights(vertex))
                other, = directions - {direction}
                expected = (-direction)**k / (other-direction)
                euler_marked = direction * other
                euler_other = (-direction) * (other-direction)
                native = locus._localization_factors(insertion)
                required = {"edge_contribution": -1 / (direction**2 * other * (other-direction)),
                            "tangent_normalization": euler_marked * euler_other,
                            "insertion_factor": euler_marked,
                            "source_curve_factor": ((-direction)**k / euler_marked
                                                    * (-direction) / euler_other)}
                for name, value in required.items():
                    require(field(native[name]) == value, f"Changed native factor {name} at power {k}")
            else:
                expected = field.zero()
            require(term == expected, f"Changed individual flag at descendant power {k}")
            total += term
        require(total == (y**k-(y-x)**k)/x == field(maps.integrate(0, 1, beta, insertion)),
                f"Changed two-flag sum at power {k}")
    print("Six fixed loci, 30 individual contributions and all 40 supported factor checks passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", type=Path, required=True)
    producer, _ = producer_source(parser.parse_args().producer)
    with tempfile.TemporaryDirectory(prefix="gw-plane-line-flags-") as directory:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            cache = Path(directory) / variable
            cache.mkdir()
            os.environ[variable] = str(cache)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        check(producer)
