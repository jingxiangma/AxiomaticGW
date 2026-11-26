#!/usr/bin/env python3
"""Find an exact certificate for the published Belorousski--Pandharipande relation.

The target is Theorem 1, equation (4), arXiv:math/9803072. Its twenty
stack-stratum diagrams are summed over all six marking assignments and
converted to raw pushforwards by their graph automorphism orders.
The witness uses four original full-stable 3-spin rows and sixteen explicit
separating pushforwards, each with its original source parameter and frame.
Exact row arithmetic does not prove geometric vanishing of those generators.
"""
import argparse
import hashlib
import importlib.metadata
from itertools import permutations
import json
import os
from pathlib import Path
import platform
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require

FRAME = "belorousski_pandharipande_mbar_2_3_v1"
RELATION_SOURCE = "arXiv:1303.1043; admcycles 1.4 original full-stable 3-spin rows"
PUBLISHED_SOURCE = "arXiv:math/9803072, Theorem 1, equation (4), page 4"
SELECTED = [1, 2, 5, 9, 16, 19, 20, 23, 31, 32, 33, 34, 35, 38, 39, 40, 41, 42, 43, 45]
SOURCE_FAMILIES = [(2, 2), (0, 4), (2, 1), (1, 1), (1, 4), (1, 2), (1, 3)]

def graph(genera, legs, edges, lp=None, hp=None):
    """Transcribe a three-marked paper diagram before any marking sum."""
    return dict(genus=genera, leg_vertices=legs, endpoints=edges,
                kappa=[[0, 0] for _ in genera], leg_psi=lp or [0, 0, 0],
                half_psi=hp or [[0, 0] for _ in edges])

# Theorem 1, equation (4), arXiv:math/9803072, in reading order.
# Labels are assigned once here and all six assignments will be summed.
PUBLISHED_TERMS = [
 ('-2',graph([2,0,0],[1,2,2],[[0,1],[1,2]])),
 ('2',graph([2,0],[1,1,1],[[0,1]],hp=[[1,0]])),
 ('3',graph([2,0],[0,1,1],[[0,1]],lp=[1,0,0])),
 ('-3',graph([2,0],[0,1,1],[[0,1]],hp=[[1,0]])),
 ('2/5',graph([1,0,1],[1,1,1],[[0,1],[1,2]])),
 ('-6/5',graph([1,0,1],[1,1,2],[[0,1],[1,2]])),
 ('12/5',graph([1,0,1],[1,2,2],[[0,1],[1,2]])),
 ('-18/5',graph([1,0,1],[0,1,2],[[0,1],[1,2]])),
 ('-6/5',graph([1,1,0],[2,2,2],[[0,1],[1,2]])),
 ('9/5',graph([1,1,0],[0,2,2],[[0,1],[1,2]])),
 ('-6/5',graph([1,1,0],[1,2,2],[[0,1],[1,2]])),
 ('1/60',graph([0,1],[0,0,0],[[0,0],[0,1]])),
 ('-3/20',graph([0,1],[0,0,1],[[0,0],[0,1]])),
 ('3/20',graph([0,1],[0,1,1],[[0,0],[0,1]])),
 ('-1/60',graph([0,1],[1,1,1],[[0,0],[0,1]])),
 # In the two-crossing diagrams the dotted left arc ends at genus 0.
 ('1/5',graph([0,1],[0,0,0],[[0,1],[0,1]])),
 ('-3/5',graph([0,1],[0,0,1],[[0,1],[0,1]])),
 ('1/5',graph([0,1],[0,1,1],[[0,1],[0,1]])),
 ('-1/10',graph([1,0],[1,1,1],[[0,0],[0,1]])),
 ('-1/10',graph([1,0],[0,1,1],[[0,0],[0,1]])),
]
def key(t):
    """Canonical decorated incidence, allowing vertex, edge and branch reorderings."""
    codes = []
    for perm in permutations(range(len(t["genus"]))):
        vertices = [(t["genus"][perm.index(v)], tuple(t["kappa"][perm.index(v)]))
                    for v in range(len(perm))]
        legs = [(perm[v], p) for v, p in zip(t["leg_vertices"], t["leg_psi"])]
        edges = sorted(tuple(sorted(zip([perm[v] for v in e], p)))
                       for e, p in zip(t["endpoints"], t["half_psi"]))
        codes.append((tuple(vertices), tuple(legs), tuple(edges)))
    return min(codes)


def relabel(t, permutation):
    """Use the inverse marking action: each new slot names its old slot."""
    return dict(t, leg_vertices=[t["leg_vertices"][permutation[i]] for i in range(3)],
                leg_psi=[t["leg_psi"][permutation[i]] for i in range(3)])


def run_search():
    from sage.all import QQ, identity_matrix, matrix, vector
    from sage.version import version
    from admcycles import TautologicalRing, admcycles, stable_graph, tautological_ring
    from admcycles.DR import algebra, graph as dr_graph, relations
    from admcycles.DR.moduli import MODULI_ST
    require(version == "10.9" and importlib.metadata.version("admcycles") == "1.4",
            "Review the environment pin")
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
            admcycles.genstobasis, admcycles.FZ_conjecture_holds)), "Online lookup active")
    rational = lambda x: [int(QQ(x).numerator()), int(QQ(x).denominator())]
    vec = lambda a: [rational(x) for x in a]
    mat = lambda a: [vec(row) for row in a]
    parameter = lambda p: {"sigma": [int(s) for s in p[0]],
        "marking_groups": [[int(label), [int(a) for a in powers]] for label, powers in p[1]]}

    def frame(g, n, r):
        ring = TautologicalRing(g, n, moduli="st", base_ring=QQ)
        classes = ring.generators(r)
        graphs, raw = [], []
        for index, element in enumerate(classes):
            require(len(element._terms) == 1, "Expected one raw graph term")
            term = next(iter(element._terms.values()))
            require(list(term.poly.coeff) == [1] and len(term.poly.monom) == 1,
                    "Expected a unit monomial coefficient")
            ka, ps = term.poly.monom[0]
            G = term.gamma
            require(all(len(p) <= 2 for p in ka), "Unexpected kappa degree")
            graphs.append({"index": index, "genus": list(map(int, G.genera())),
                "leg_vertices": [int(G.vertex(l)) for l in range(1, n + 1)],
                "endpoints": [[int(G.vertex(h)) for h in e] for e in G.edges()],
                "kappa": [[int(p[j]) if j < len(p) else 0 for j in range(2)] for p in ka],
                "leg_psi": [int(ps.get(l, 0)) for l in range(1, n + 1)],
                "half_psi": [[int(ps.get(h, 0)) for h in e] for e in G.edges()]})
            raw.append(element.vector(r))
        require(matrix(QQ, raw) == identity_matrix(QQ, len(classes)), "Changed raw basis")
        return ring, graphs

    genus, degree, marks = 2, 2, (1, 2, 3)
    ring, graphs = frame(genus, 3, degree)
    require(len(graphs) == 100, "Changed target frame")
    keys = {key(g): i for i, g in enumerate(graphs)}
    require(len(keys) == 100, "Repeated target graph")
    permutations_table = [[keys[key(relabel(g, p))] for g in graphs]
                          for p in permutations(range(3))]
    autos = [int(dr_graph.autom_count(i, genus, degree, marks, MODULI_ST)) for i in range(100)]
    target, published = vector(QQ, 100), []
    for c, G in PUBLISHED_TERMS:
        destinations = [keys[key(relabel(G, p))] for p in permutations(range(3))]
        order = autos[destinations[0]]
        require(all(autos[i] == order for i in destinations), "Orbit order changed")
        for i in destinations:
            target[i] += QQ(c) / order
        published.append({"coefficient": rational(QQ(c)), "graph": G,
            "automorphism": order, "destinations": destinations})

    params = relations.FZ_param_list(3 * degree - genus - 1, marks)
    require(len(params) == 16, "Changed interior generators")
    full = relations.FZ_matrix(genus, degree, marks, MODULI_ST)
    require(full.dimensions() == (65, 100), "Changed full relation matrix")
    originals, provenance = [], []
    for i in SELECTED[:4]:
        a = vector(QQ, [relations.FZ_coeff(j, params[i], genus, degree, marks, MODULI_ST)
                        for j in range(100)])
        require(a == full[i], "Interior provenance changed")
        originals.append(a)
        provenance.append({"kind": "interior", "upstream_index": i,
                           "parameter": parameter(params[i])})
    source_frames = [frame(g, n, 1)[1] for g, n in SOURCE_FAMILIES]
    count = 16
    # Enumerate the original boundary_FZ ordering and retain explicit vertex replacements.
    for base_index, G in enumerate(dr_graph.all_strata(genus, 1, marks, MODULI_ST)):
        for orbit in relations.graph_count_automorphisms(G, True):
            v = orbit[0]
            if any(relations.R(G.M[v, j][0]) != G.M[v, j] for j in range(G.M.ncols())):
                continue
            g, n = int(G.M[v, 0][0]), int(G.degree(v))
            if 3 < g + 1 or relations.dim_form(g, n, MODULI_ST) < 1:
                continue
            cols = dr_graph.all_strata(g, 1, tuple(range(1, n + 1)), MODULI_ST)
            destinations = []
            for source in cols:
                H = dr_graph.Graph(G.M)
                H.replace_vertex_with_graph(v, source)
                destinations.append(int(dr_graph.num_of_stratum(H, genus, degree, marks, MODULI_ST)))
            for p in relations.reduced_FZ_param_list(G, v, g, n, 3 - g - 1):
                if count in SELECTED:
                    require(all(i >= 0 for i in destinations), "Dropped source column")
                    coefficients = [relations.FZ_coeff(i, p, g, 1, tuple(range(1, n + 1)),
                                                       MODULI_ST) for i in range(len(cols))]
                    a = vector(QQ, 100)
                    for i, x in zip(destinations, coefficients):
                        a[i] += x
                    require(a == full[count], "Separating provenance changed")
                    originals.append(a)
                    provenance.append({"kind": "separating", "upstream_index": count,
                        "base_index": base_index, "vertex_one_based": int(v),
                        "source_family": SOURCE_FAMILIES.index((g, n)),
                        "parameter": parameter(p), "destinations": destinations,
                        "coefficients": vec(coefficients)})
                count += 1
    require(count == 65 and len(originals) == 20, "Incomplete generator enumeration")
    forward = matrix(QQ, [algebra.convert_vector_to_monomial_basis(e, genus, degree, marks,
        MODULI_ST) for e in identity_matrix(QQ, 100)])
    inverse = matrix(QQ, [algebra.convert_vector_to_pushforward_basis(e, genus, degree, marks,
        MODULI_ST) for e in identity_matrix(QQ, 100)])
    expected = identity_matrix(QQ, 100); expected[1, 0] = 1
    require(forward == expected and forward * inverse == identity_matrix(QQ, 100),
            "Kappa conversion changed")
    unsym = matrix(QQ, originals) * forward
    symmetric = []
    for a in unsym:
        b = vector(QQ, 100)
        for p in permutations_table:
            for i, x in enumerate(a):
                b[p[i]] += x
        symmetric.append(b)
    rows = matrix(QQ, symmetric)
    witness = rows.solve_left(target)
    require(witness * rows == target, "Failed exact BP membership")
    # Diagnostic only: all degree-four monomials in the three external psi classes.
    relation_class = ring.from_vector(target, degree)
    tests = [(relation_class * ring.psi(1) ** a * ring.psi(2) ** b *
              ring.psi(3) ** (4 - a - b)).evaluate() for a in range(5) for b in range(5 - a)]
    require(all(x == 0 for x in tests), "Intersection diagnostic failed")
    return {"schema_version": 1, "frame": FRAME, "locus": "full_stable", "genus": 2,
        "markings": [0, 1, 2], "codimension": 2, "normalization": "raw_gluing_pushforward",
        "source_label_map": [[1, 0], [2, 1], [3, 2]], "relation_source": RELATION_SOURCE,
        "published_source": PUBLISHED_SOURCE, "published_terms": published,
        "graphs": graphs, "source_families": [{"genus": g, "markings": n, "codimension": 1,
            "graphs": gs} for (g, n), gs in zip(SOURCE_FAMILIES, source_frames)],
        "generator_provenance": provenance, "column_factors": [[1, 1]] * 100,
        "automorphism_counts": autos, "original_rows": mat(originals),
        "unsymmetrized_rows": mat(unsym), "rows": mat(rows), "requested": vec(target),
        "witness": vec(witness), "permutation_destinations": permutations_table,
        "pushforward_to_monomial_off_diagonal": [[1, 0, [1, 1]]],
        "monomial_to_pushforward_off_diagonal": [[1, 0, [-1, 1]]],
        "environment": {"sage": version, "admcycles": "1.4", "python": platform.python_version(),
                        "architecture": platform.machine()},
        "producer_source_sha256": {Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
            for m in (admcycles, stable_graph, tautological_ring, algebra, dr_graph, relations)},
        "exploration": {"online_lookup": False, "cache_ephemeral": True,
            "raw_basis_identity_checked": True, "full_row_count": 65, "selected_row_count": 20,
            "selected_rank": int(rows.rank()), "intersection_tests": vec(tests)},
        "scope": "The exact published BP equation is derived from original 3-spin rows and explicit "
            "separating graph operations. Geometric source-row vanishing remains conditional. "
            "Neither this search nor its intersection diagnostics certify numerical GW invariants."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-bp-") as directory:
        for name in ("DOT_SAGE", "ADMCYCLES_CACHE_DIR", "MPLCONFIGDIR", "XDG_CACHE_HOME"):
            location = Path(directory) / name
            location.mkdir()
            os.environ[name] = str(location)
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        result = run_search()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
