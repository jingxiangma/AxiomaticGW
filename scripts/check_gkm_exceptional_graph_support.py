#!/usr/bin/env python3
"""Check pre-integration graph support on the pinned two-point blowup."""
import argparse
import os
from pathlib import Path
import sys
import tempfile

from export_gkm_inputs import producer_source, require, target_specifications


def check(producer):
    from sage.all import Fan, LaurentPolynomialRing, ZZ
    from sage.version import version
    from admcycles.admcycles import set_online_lookup, set_online_lookup_default
    from importlib.metadata import version as package_version

    require(version == "10.9" and package_version("admcycles") == "1.4", "Changed Sage or admcycles")
    set_online_lookup(False)
    set_online_lookup_default(False)
    sys.path.insert(0, str(producer))
    import gkm_localization
    from gkm_localization import StableMapGKM, StableMapsGKM, toric_target_from_fan
    require(Path(gkm_localization.__file__).resolve().parent == producer / "gkm_localization",
            "Imported a different GKM producer")
    spec = next(s for s in target_specifications() if s["id"] == "X2")
    torus = LaurentPolynomialRing(ZZ, names=("x", "y"))
    target = toric_target_from_fan(Fan(cones=spec["cones"], rays=spec["rays"]), torus,
                                   curve_basis=spec["curves"], name="X2")
    points = sorted(target.fixed_points())
    maps = StableMapsGKM(target)
    curve = ZZ**3
    mixed = curve((1, 1, 0))
    for genus in (0, 1, 2):
        for markings in (0, 1, 2):
            require(not maps.fixed_loci(genus, markings, mixed), "Unexpected connected fixed locus")
    for coordinates, endpoints in (((1, 0, 0), (1, 2)), ((0, 1, 0), (3, 4))):
        loci = maps.fixed_loci(0, 0, curve(coordinates))
        require(len(loci) == 1, "Missing primitive exceptional locus")
        locus, = loci
        edge, = locus.edges()
        images = sorted(points.index(locus.image(v)) for v in locus.edge_vertices(edge))
        require(images == list(endpoints) and locus.edge_degree(edge) == 1 and
                locus.degree() == curve(coordinates), "Changed full edge support")
    # Three covers, one of each primitive class, form a path that includes the line.
    require(any(len(g.edges()) == 3 and g._component_count() == 1
                for g in maps.fixed_loci(0, 0, curve((1, 1, 1)))), "Missing connected path via L")
    # Direct constructor checks edge labels and positive covers, but accepts disconnected inputs.
    raw = {i: {i: (0, set(), points[i])} for i in (1, 2, 3, 4)}
    raw[1][2] = 1
    raw[3][4] = 1
    disjoint = StableMapGKM(raw, target)
    require(disjoint.degree() == mixed and disjoint._component_count() == 2,
            "Disconnected control no longer realizes the mixed total")
    print("9 empty fixed-locus enumerations, both exceptional edge controls, "
          "a connected path through L and a disconnected mixed graph passed.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer", required=True, type=Path)
    args = parser.parse_args()
    producer, _ = producer_source(args.producer)
    with tempfile.TemporaryDirectory(prefix="gw-exceptional-graph-") as directory:
        for variable in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            cache = Path(directory) / variable
            cache.mkdir()
            os.environ[variable] = str(cache)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        check(producer)
