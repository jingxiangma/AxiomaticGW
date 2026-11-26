#!/usr/bin/env python3
"""Expand the fixed genus-two square/product relations by actual forgetful pullback.

No relation search or higher-arity geometric row is used. The offline Lean
consumer compares these coordinates with its independently computed signed
cotangent expansion in the existing Mbar(2,2) and Mbar(2,3) graph frames.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require
from search_belorousski_pandharipande import key

ROOT = Path(__file__).resolve().parents[1]
CASES = (("square_two", "square", 1, 2), ("square_three", "square", 1, 3),
         ("product_three", "product", 2, 3))
SOURCE_FILES = ("genus-two-psi-square-exploration.json",
                "genus-two-psi-product-exploration.json", "belorousski-pandharipande.json")


def run_search():
    from sage.all import QQ, vector
    from sage.version import version
    from admcycles import TautologicalRing, admcycles, stable_graph, tautological_ring
    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review the environment pins")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    rational = lambda q: [int(q.numerator()), int(q.denominator())]
    results = []
    for name, kind, old, new in CASES:
        source = json.loads((ROOT / f"environments/genus-two-psi-{kind}-exploration.json").read_text())
        frame = json.loads((ROOT / "environments" / (SOURCE_FILES[1] if new == 2 else SOURCE_FILES[2])).read_text())
        ring = TautologicalRing(2, old, moduli="st", base_ring=QQ)
        relation = ring.from_vector(vector(QQ, [QQ(a)/b for a, b in source["requested"]]), 2)
        pulled = relation.forgetful_pullback(list(range(old + 1, new + 1)))
        v = pulled.vector(2)
        require(len(v) == len(frame["graphs"]), "Changed coordinate frame")
        for e, held in zip(pulled.parent().generators(2), frame["graphs"]):
            t = next(iter(e._terms.values()))
            G = t.gamma
            ka, ps = t.poly.monom[0]
            raw = {"genus": list(map(int, G.genera())),
                   "leg_vertices": [int(G.vertex(i)) for i in range(1, new+1)],
                   "endpoints": [[int(G.vertex(h)) for h in edge] for edge in G.edges()],
                   "kappa": [[int(p[i]) if i < len(p) else 0 for i in range(2)] for p in ka],
                   "leg_psi": [int(ps.get(i, 0)) for i in range(1, new+1)],
                   "half_psi": [[int(ps.get(h, 0)) for h in edge] for edge in G.edges()]}
            require(key(raw) == key(held), "Existing graph frame does not match")
        leading = ((pulled.parent().psi(1)**2) if kind == "square" else
                   (pulled.parent().psi(1)*pulled.parent().psi(2))).vector(2)
        lead = leading.nonzero_positions()
        require(len(lead) == 1 and leading[lead[0]] == v[lead[0]] == 1,
                "Leading monomial changed")
        for i in v.nonzero_positions():
            g = frame["graphs"][i]
            require(not any(any(p) for p in g["kappa"]), "Unexpected kappa correction")
            for vertex, genus in enumerate(g["genus"]):
                powers = sum(p for w, p in zip(g["leg_vertices"], g["leg_psi"]) if w == vertex)
                powers += sum(p for e, ps in zip(g["endpoints"], g["half_psi"])
                              for w, p in zip(e, ps) if w == vertex)
                require(i == lead[0] or genus < 2 or powers <= 1,
                        "Remainder does not reduce genus-two powers")
        results.append({"name": name, "source_kind": kind, "old_arity": old,
                        "new_arity": new, "normalization": "raw_gluing_pushforward",
                        "coordinates": [rational(q) for q in v], "leading_column": int(lead[0]),
                        "support_size": len(v.nonzero_positions())})
    return {"schema_version": 1, "frame": "genus_two_psi_pullbacks_v1", "cases": results,
            "source_sha256": {p: hashlib.sha256((ROOT/"environments"/p).read_bytes()).hexdigest()
                              for p in SOURCE_FILES},
            "producer_sha256": {Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                                for m in (admcycles, stable_graph, tautological_ring)},
            "environment": {"sage": version, "admcycles": "1.4"},
            "scope": "Exact pullbacks of the held square/product relations; primitive geometry "
                     "and original source validity remain explicit. No L24 or numeric value is certified."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="gw-psi-pullback-") as tmp:
        for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            p = Path(tmp)/name
            p.mkdir()
            os.environ[name] = str(p)
        (Path(os.environ["DOT_SAGE"])/"admcycles").mkdir()
        result = run_search()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")


if __name__ == "__main__":
    main()
