#!/usr/bin/env python3
"""Export raw Hodge-strata candidates on Mbar_(2,1), using pinned admcycles.

This script has no Sage/admcycles imports at module scope. Run it with the
pinned Sage environment's Python; offline certificate replay needs no Sage. The output is
nine actual admcycles decorated-strata representatives, not a certified
Hodge class, CohFT, GW class, integration result or relation certificate.
The five degree components of each ordered pair are explicit, including zeros.
"""

import argparse
from fractions import Fraction
import hashlib
import importlib.metadata
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
REPOSITORY = Path(__file__).resolve().parents[1]
INSTALLED_PINS = {
    'tautological_ring.py': 'c9cf9b46fa8c7f2207d6d0ebc3f3565518f6f29d324bb6b280c1626a772bbd12',
    'admcycles.py': '19e9e77c58299b387abadab76f2e1f1b1b2b63808f3dbbd0e44499a930db9a1b',
    'stable_graph.py': 'aa9b81ae274660b2d44cf474390a8b0c3a7865cfa6deaa06d005ae96dfdbd3ca',
    'moduli.py': '81bbe21a06daf0a8f0481dd793e6635da8d6767fb563684ed96204e2dcc50e71',
    'DR/graph.py': '3c4c4f833989177f055710c067e77817113efd4062cdab105e56162155949481',
    'DR/algebra.py': '7d684ffc9c04d77434a9a2e9d52d4a7c79b159693bc5d5989ee443cbdcc724d1',
}
REPOSITORY_PINS = {
    'scripts/export_admcycles_certificate.py':
        '28b9d7b9c81d10ef241f6a7a9082cf29047967ddf03ddf1d4433057b6b8d05f8',
    'scripts/explore_decorated_pullback.py':
        '1977a3348bbb7f97778ba174514d5ff67a58a455592b7663bdcb8d2738b2ff6d',
}
KAPPA_INDICES = [1, 2, 3, 4]
DEGREES = [0, 1, 2, 3, 4]
KAPPA_CONVENTION = 'kappa_a = pi_*(psi_new^(a+1)); monomial powers'
LIMITATIONS = [
    'Installed source pins cover the named adapter/formula files, not every Sage dependency.',
    'admcycles internally applies local component-dimension filtering during construction.',
    'GRR/Chern formula and product/common-refinement geometry are not proved by this export.',
    'No basis_vector, FZ quotient, evaluate, degree_cap or integration call is made.',
    'No Lean graph, relation or geometric realization acceptance is claimed.',
    'No constant-map virtual Euler/stabilization or GW/CohFT gluing identification is claimed.',
    'Equivariant coefficients and their grading must be attached and checked separately.',
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def natural(value, message):
    # Includes Sage integers, but rejects booleans, fractions and lossy casts.
    require(not isinstance(value, bool), message)
    result = int(value)
    require(value == result and result >= 0, message)
    return result


def rational_pair(coefficient, QQ, shared_rational):
    q = QQ(coefficient)
    pair = [int(q.numerator()), int(q.denominator())]
    decoded = shared_rational(pair)
    require(decoded == Fraction(*pair), 'Shared rational decoder changed the coefficient')
    return [decoded.numerator, decoded.denominator]


def graph_packet(graph, kappa, psi):
    """Reuse the decorated-pullback field convention, retaining all kappa data.

    No isomorphism canonicalization or automorphism division is performed.
    Source edge order labels Fin edge and source tuple order labels its branches.
    """
    genera = [natural(g, 'Invalid vertex genus') for g in graph.genera()]
    vertices = len(genera)
    require(vertices > 0 and int(graph.num_verts()) == vertices, 'Invalid vertex frame')
    markings = [natural(m, 'Invalid marking') for m in graph.list_markings()]
    require(sorted(markings) == [1], 'Only the original external marking 1 is supported')
    edges = []
    half_psi = []
    half_labels = []
    used = {1}
    for source_edge in graph.edges():
        require(len(source_edge) == 2, 'An edge must have exactly two branches')
        flags = [natural(h, 'Invalid halfedge label') for h in source_edge]
        require(all(h > 1 and h not in used for h in flags) and flags[0] != flags[1],
                'Repeated, external or nonpositive internal flag')
        used.update(flags)
        half_labels.append(flags)
        edges.append([natural(graph.vertex(h), 'Invalid endpoint') for h in flags])
        half_psi.append([natural(psi.get(h, 0), 'Invalid node psi power') for h in flags])
    require(all(natural(h, 'Invalid psi flag') in used for h in psi),
            'Psi decoration on an unknown flag')
    require(all(natural(p, 'Invalid psi power') >= 0 for p in psi.values()),
            'Invalid psi power')
    legs = [natural(graph.vertex(1), 'Invalid marking vertex')]
    require(all(v < vertices for e in edges for v in e) and legs[0] < vertices,
            'Incidence outside the vertex frame')
    source_flags = []
    for v in range(vertices):
        row = [natural(h, 'Invalid vertex flag') for h in graph.legs(v, copy=False)]
        require(all(h in used and int(graph.vertex(h)) == v for h in row),
                'Unsupported or inconsistent vertex flag')
        source_flags.extend(row)
    require(len(source_flags) == len(used) and set(source_flags) == used,
            'Unencoded or repeated graph flag')
    require(len(kappa) == vertices, 'Wrong kappa vertex count')
    kappas = []
    for powers in kappa:
        powers = [natural(p, 'Invalid kappa power') for p in powers]
        require(not any(powers[4:]), 'A nonzero kappa index above four is unsupported')
        kappas.append((powers[:4] + [0] * 4)[:4])
    degree = len(edges) + sum(sum(i * p for i, p in zip(KAPPA_INDICES, row))
                              for row in kappas)
    leg_psi = [natural(psi.get(1, 0), 'Invalid external psi power')]
    degree += sum(leg_psi) + sum(sum(row) for row in half_psi)
    packet = {'genus': genera, 'leg_vertices': legs, 'endpoints': edges,
              'kappa': kappas, 'leg_psi': leg_psi, 'half_psi': half_psi,
              'admcycles_halfedge_labels': half_labels, 'codimension': degree}
    validate_graph(packet)
    return packet


def validate_graph(graph):
    """Exact structural checks on emitted finite incidence data; no class proof."""
    vertices = len(graph['genus'])
    edges = graph['endpoints']
    require(vertices > 0 and len(graph['leg_vertices']) == len(graph['leg_psi']) == 1,
            'Wrong graph arity')
    require(len(graph['kappa']) == vertices and
            all(len(row) == 4 for row in graph['kappa']), 'Wrong kappa shape')
    require(len(edges) == len(graph['half_psi']) ==
            len(graph['admcycles_halfedge_labels']), 'Wrong edge decoration shape')
    require(all(len(e) == 2 for e in edges + graph['half_psi'] +
                graph['admcycles_halfedge_labels']), 'Wrong branch arity')
    for values in [graph['genus'], graph['leg_vertices'], graph['leg_psi']] + \
            graph['kappa'] + edges + graph['half_psi'] + graph['admcycles_halfedge_labels']:
        require(all(type(v) is int and v >= 0 for v in values), 'Non-natural graph datum')
    require(all(v < vertices for v in graph['leg_vertices']) and
            all(v < vertices for e in edges for v in e), 'Endpoint out of bounds')
    labels = [h for row in graph['admcycles_halfedge_labels'] for h in row]
    require(all(h > 1 for h in labels) and len(set(labels)) == len(labels),
            'Bad internal flag labels')
    reached = {0}
    while True:
        enlarged = reached | {v for e in edges if any(w in reached for w in e) for v in e}
        if enlarged == reached:
            break
        reached = enlarged
    require(len(reached) == vertices, 'Disconnected graph')
    require(sum(graph['genus']) + len(edges) + 1 - vertices == 2, 'Wrong total genus')
    for v, g in enumerate(graph['genus']):
        valence = graph['leg_vertices'].count(v) + sum(e.count(v) for e in edges)
        require(2 * g + valence >= 3, 'Unstable vertex')
    degree = len(edges) + sum(sum(i * p for i, p in zip(KAPPA_INDICES, row))
                              for row in graph['kappa'])
    degree += sum(graph['leg_psi']) + sum(sum(row) for row in graph['half_psi'])
    require(type(graph['codimension']) is int and degree == graph['codimension'] and
            degree in DEGREES, 'Wrong or unsupported codimension')


def encode_class(element, expected_degree, QQ, shared_rational):
    terms = []
    zero_coefficients = 0
    for term in element._terms.values():
        require(len(term.poly.monom) == len(term.poly.coeff), 'Polynomial shape mismatch')
        for monomial, coefficient in zip(term.poly.monom, term.poly.coeff):
            require(len(monomial) == 2, 'Unsupported decoration monomial')
            kappa, psi = monomial
            graph = graph_packet(term.gamma, kappa, psi)
            pair = rational_pair(coefficient, QQ, shared_rational)
            if pair[0] == 0:
                zero_coefficients += 1
                continue
            require(graph['codimension'] == expected_degree, 'Hodge product is not homogeneous')
            terms.append({'coefficient': pair, 'graph': graph})
    # Sorting only orders the source representations; no terms are identified.
    terms.sort(key=lambda term: json.dumps(term, sort_keys=True, separators=(',', ':')))
    return [{'codimension': d, 'terms': terms if d == expected_degree else []}
            for d in DEGREES], zero_coefficients


def installed_admcycles_directory():
    """Locate the top-level package without importing or executing its source."""
    spec = importlib.util.find_spec('admcycles')
    require(spec is not None and spec.origin is not None and
            spec.submodule_search_locations is not None,
            'Run this exporter with the pinned Sage/admcycles Python environment')
    return Path(spec.origin).resolve().parent


def verify_sources(repository, installed):
    sources = []
    for root, pins in [(installed, INSTALLED_PINS), (repository, REPOSITORY_PINS)]:
        for relative, expected in pins.items():
            path = root / relative
            require(sha256(path) == expected, f'Source pin changed: {path}')
            sources.append({'path': str(path.resolve()), 'sha256': expected})
    return sources


def deferred_export(repository):
    installed = installed_admcycles_directory()
    sources = verify_sources(repository, installed)
    helper_path = repository / 'scripts/export_admcycles_certificate.py'
    spec = importlib.util.spec_from_file_location('held_rational_decoder', helper_path)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    # These are the only Sage/admcycles imports in this script, intentionally deferred.
    from sage.all import QQ
    from sage.version import version
    import admcycles
    from admcycles import TautologicalRing
    from admcycles import admcycles as legacy

    require(version == '10.9' and importlib.metadata.version('admcycles') == '1.4',
            'Review the pinned Sage/admcycles runtime')
    require(Path(admcycles.__file__).resolve().parent == installed,
            'A different admcycles installation was imported')
    legacy.set_online_lookup(False)
    legacy.set_online_lookup_default(False)
    require(all(not f.go_online for f in (legacy.generating_indices,
            legacy.genstobasis, legacy.FZ_conjecture_holds)), 'Online lookup is active')
    ring = TautologicalRing(2, 1, moduli='st', base_ring=QQ)
    lambdas = [ring.lambdaclass(k, pull=True) for k in range(3)]
    pairs = []
    for a in range(3):
        for b in range(3):
            components, zeros = encode_class(lambdas[a] * lambdas[b], a + b,
                                             QQ, helper.rational)
            pairs.append({'lambda_indices': [a, b], 'expected_codimension': a + b,
                          'components': components, 'source_zero_coefficients': zeros})
    packet = {
        'schema_version': 1, 'kind': 'admcycles.hodge_raw_strata_packet',
        'proof_status': 'candidate_strata_representatives',
        'moduli': {'genus': 2, 'markings': 1, 'locus': 'full_stable', 'dimension': 4},
        'external_label_map': [[1, 0]], 'coefficient_ring': 'QQ',
        'normalization': 'raw_gluing_pushforward', 'kappa_indices': KAPPA_INDICES,
        'kappa_convention': KAPPA_CONVENTION, 'degree_components': DEGREES,
        'construction': {'lambda': 'TautologicalRing(2,1).lambdaclass(k,pull=True)',
                         'product': 'admcycles TautologicalClass.__mul__',
                         'coordinates': 'raw _terms/decstratum.poly monomials'},
        'pairs': pairs,
        'environment': {'sage': version, 'admcycles': importlib.metadata.version('admcycles'),
                        'python_executable': sys.executable},
        'provenance': {'sources': sources, 'exporter_sha256': sha256(Path(__file__))},
        'checks': {'all_nine_ordered_pairs': True, 'all_five_components_explicit': True,
                   'graph_structure': True, 'homogeneity': True,
                   'ephemeral_cache': True, 'online_lookup': False},
        'claims': {'lean_acceptance': False, 'geometric_hodge_identification': False,
                   'gw_class_identification': False, 'cohft': False},
        'limitations': LIMITATIONS,
    }
    require(json.loads(json.dumps(packet)) == packet, 'JSON round-trip changed the packet')
    return packet


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', type=Path, default=REPOSITORY)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an existing candidate packet')
    with tempfile.TemporaryDirectory(prefix='axiomatic-gw-hodge-strata-') as temporary:
        for variable, directory in [('DOT_SAGE', 'sage'), ('ADMCYCLES_CACHE_DIR', 'admcycles'),
                                    ('MPLCONFIGDIR', 'matplotlib'), ('XDG_CACHE_HOME', 'xdg')]:
            location = Path(temporary) / directory
            location.mkdir()
            os.environ[variable] = str(location)
        (Path(os.environ['DOT_SAGE']) / 'admcycles').mkdir()
        packet = deferred_export(args.repository.resolve())
    with args.output.open('x') as output:
        output.write(json.dumps(packet, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'output': str(args.output.resolve()), 'sha256': sha256(args.output),
                      'ordered_pairs': 9, 'explicit_components': 45,
                      'nonzero_source_terms': sum(len(c['terms']) for p in packet['pairs']
                                                 for c in p['components']),
                      'proof_status': packet['proof_status']}, sort_keys=True))


if __name__ == '__main__':
    main()
