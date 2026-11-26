#!/usr/bin/env python3
"""Compare complete L24 surface equations with independent admcycles contractions.

Graph contraction and signed pullback use admcycles incidence data. Low-genus
numbers are shared outputs of the proved Lean algorithms, not independent GW
references. The report is exploration evidence; the imported Lean theorems
supply the general conditional soundness of the surface equations.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
from export_admcycles_certificate import require, unique_object
from explore_surface_bp import collect, contract, digest, energy, query_key

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'environments/l24-normalization-exploration.json'
SOURCE_SHA256 = '227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7'
EXPECTED_CASES = {
    'p2_zero_HH11': (0, (0,), 0, (1, 1, 0, 0)),
    'p2_line_HHHP': (0, (1,), 0, (1, 1, 1, 2)),
    'p2_line_HHHH_p': (0, (1,), 1, (1, 1, 1, 1)),
    'f1_E_EEE1': (1, (1, 0), 0, (3, 3, 3, 0)),
    'f1_F_EHHH': (1, (0, 1), 0, (3, 1, 1, 1)),
    'bl2_E1_E1E1E11': (2, (1, 0, 0), 0, (3, 3, 3, 0)),
    'bl2_E2_E1E1E11': (2, (0, 1, 0), 0, (3, 3, 3, 0)),
    'bl2_L_E1E2H1': (2, (0, 0, 1), 0, (3, 4, 1, 0)),
    'bl2_E1E2_E1E1E2E2': (2, (1, 1, 0), 0, (3, 3, 4, 4)),
}


def explore(payload, lean_source):
    from sage.all import QQ, matrix
    from sage.version import version
    from admcycles import StableGraph, TautologicalRing, admcycles, stable_graph, tautological_ring

    require(version == '10.9' and importlib.metadata.version('admcycles') == '1.4',
            'Review Sage/admcycles pins')
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256, 'L24 source changed')
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    require(all(not f.go_online for f in (admcycles.generating_indices,
                admcycles.genstobasis, admcycles.FZ_conjecture_holds)), 'Online lookup active')
    source = json.loads(SOURCE.read_bytes(), object_pairs_hook=unique_object)
    data = json.loads(payload, object_pairs_hook=unique_object)
    require(type(data['schema_version']) is int and data['schema_version'] == 1,
            'Unexpected Lean export version')
    names = [c['name'] for c in data['cases']]
    require(len(names) == len(EXPECTED_CASES) and set(names) == set(EXPECTED_CASES),
            'Incomplete case coverage')
    base = TautologicalRing(2, 4, moduli='st', base_ring=QQ)
    primitive_ids = {i for i, c in source['primitive'] if c[0]}
    require(len(source['full']) == 721 and len(primitive_ids) == 18, 'Changed complete support')

    def raw(graph):
        legs = [[] for _ in graph['genus']]
        psi = {}
        require(not any(any(k) for k in graph['kappa']), 'Unexpected kappa decoration')
        for flag, (v, p) in enumerate(zip(graph['leg_vertices'], graph['leg_psi']), 1):
            legs[v].append(flag)
            if p:
                psi[flag] = p
        edges = []
        for edge, (ends, powers) in enumerate(zip(graph['endpoints'], graph['half_psi'])):
            flags = (5 + 2 * edge, 6 + 2 * edge)
            edges.append(flags)
            for flag, v, p in zip(flags, ends, powers):
                legs[v].append(flag)
                if p:
                    psi[flag] = p
        return base(StableGraph(graph['genus'], legs, edges), psi=psi)

    @lru_cache(None)
    def relation(n, primitive_only=False, omit_tail_corrections=False, erase_node_powers=False):
        result = []
        for index, coefficient in source['full']:
            if primitive_only and index not in primitive_ids:
                continue
            original = raw(source['graphs'][index])
            pulled = original if n == 0 else original.forgetful_pullback(list(range(5, 5 + n)))
            for term in pulled._terms.values():
                for (kappa, psi), c in zip(term.poly.monom, term.poly.coeff):
                    require(not any(any(v) for v in kappa), 'Unexpected pulled kappa term')
                    c = QQ(c)
                    c = Fraction(int(c.numerator()), int(c.denominator()))
                    if omit_tail_corrections and c < 0:
                        continue
                    if erase_node_powers:
                        psi = {f: p for f, p in psi.items() if f <= 4 + n}
                    result.append((term.gamma, psi, Fraction(*coefficient) * c))
        return result

    def contracted(name, **mutation):
        r, beta, n, labels = EXPECTED_CASES[name]
        positive_metric = mutation.pop('positive_metric', False)
        answer = defaultdict(Fraction)
        for graph, psi, coefficient in relation(n, **mutation):
            terms = contract(graph, psi, coefficient, r, beta, labels + (2,) * n, positive_metric)
            for monomial, c in terms.items():
                answer[monomial] += c
        return {m: c for m, c in answer.items() if c}

    reports, raw_by_name, reduced_by_name = [], {}, {}
    for case in data['cases']:
        name = case['name']
        print('Comparing ' + name, file=sys.stderr, flush=True)
        r, beta, n, labels = EXPECTED_CASES[name]
        require((case['blowups'], tuple(case['curve']), case['additional_markings'],
                 tuple(case['labels'])) == (r, beta, n, labels), 'Request changed: ' + name)
        raw_exact = contracted(name)
        require(raw_exact == collect(case['symbolic_terms']), 'Raw contraction: ' + name)
        low = {query_key(q['query']): Fraction(*q['value']) for q in case['lower_values']}
        require(len(low) == len(case['lower_values']), 'Repeated terminal query')
        reduced = defaultdict(Fraction)
        for monomial, coefficient in raw_exact.items():
            high = []
            for query in monomial:
                if query[0] <= 1:
                    require(query in low, 'Missing lower-genus substitution')
                    coefficient *= low[query]
                else:
                    high.append(query)
            reduced[tuple(high)] += coefficient
        reduced = {m: c for m, c in reduced.items() if c}
        require(reduced == collect(case['genus_two_terms']), 'Partial reconstruction: ' + name)
        require(all(len(m) <= 1 for m in reduced), 'Nonlinear residual monomial')
        unknowns = [m[0] for m in reduced if m]
        require(all(q[0] == 2 and all(x <= b for x, b in zip(q[1], beta)) for q in unknowns),
                'Wrong genus or full-class support')
        smaller = [q for q in unknowns if q[1] != beta]
        require(all(energy(r, q[1]) < energy(r, beta) for q in smaller), 'No strict decrease')
        constant = reduced.get((), Fraction(0))
        reports.append({
            'name': name, 'signed_graph_occurrences': len(relation(n)),
            'raw_monomials': len(raw_exact), 'affine_monomials': len(reduced),
            'same_class_unknowns': len(unknowns) - len(smaller),
            'smaller_class_unknowns': len(smaller), 'lower_genus_substitutions': len(low),
            'constant': [constant.numerator, constant.denominator],
            'raw_sha256': digest(raw_exact), 'affine_sha256': digest(reduced),
            'raw_equal': True, 'partial_reconstruction_equal': True,
        })
        raw_by_name[name], reduced_by_name[name] = raw_exact, reduced

    rejected = []
    mutations = [
        ('omit_703_nonprimitive_terms', {'primitive_only': True}, list(EXPECTED_CASES)),
        ('erase_node_powers', {'erase_node_powers': True}, list(EXPECTED_CASES)),
        ('positive_exceptional_metric', {'positive_metric': True}, ['f1_E_EEE1', 'f1_F_EHHH']),
        ('omit_negative_tail_corrections', {'omit_tail_corrections': True}, ['p2_line_HHHH_p']),
    ]
    for name, mutation, candidates in mutations:
        detected = next((case for case in candidates
                         if contracted(case, **mutation) != raw_by_name[case]), None)
        require(detected is not None, 'Mutation survived: ' + name)
        rejected.append({'mutation': name, 'detected_by': detected})
    require(raw_by_name['bl2_E1_E1E1E11'] != raw_by_name['bl2_E2_E1E1E11'],
            'Equal-energy classes identified')
    rejected.append({'mutation': 'replace_full_curve_by_energy',
                     'detected_by': ['bl2_E1_E1E1E11', 'bl2_E2_E1E1E11']})
    ranks = []
    for r, beta in sorted({(v[0], v[1]) for v in EXPECTED_CASES.values()}):
        family = [reduced_by_name[name] for name, v in EXPECTED_CASES.items() if v[:2] == (r, beta)]
        columns = sorted({m[0] for p in family for m in p if m and m[0][1] == beta})
        rows = [[QQ(p.get((q,), 0)) for q in columns] for p in family]
        ranks.append({'blowups': r, 'curve': beta, 'equations': len(rows),
                      'same_class_unknowns': len(columns),
                      'rank': int(matrix(QQ, len(rows), len(columns), sum(rows, [])).rank())})
    sources = [Path(__file__).resolve(), ROOT / 'scripts/explore_surface_bp.py', SOURCE,
               ROOT / 'AxiomaticGW/Surfaces/L24.lean', ROOT / 'AxiomaticGW/Tautological/L24GW.lean',
               ROOT / 'AxiomaticGW/Tautological/L24Gluing.lean',
               ROOT / 'AxiomaticGW/Tautological/Fixtures/L24Claims.lean',
               ROOT / 'AxiomaticGW/Tautological/L24Terms.lean',
               ROOT / 'AxiomaticGW/Surfaces/GenusTwoCachedTerms.lean',
               ROOT / 'AxiomaticGW/Surfaces/L24Terms.lean']
    modules = [Path(m.__file__) for m in (admcycles, stable_graph, tautological_ring)]
    return {
        'schema_version': 1, 'scope': 'Full L24 ancestor equations; no solved genus-two recursion.',
        'sage': version, 'admcycles': importlib.metadata.version('admcycles'),
        'online_lookup': False, 'lean_payload_sha256': hashlib.sha256(payload).hexdigest(),
        'lean_source_sha256': hashlib.sha256(lean_source).hexdigest(),
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sources},
        'admcycles_module_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in modules},
        'cases': reports, 'mutations_rejected': rejected, 'sample_matrix_ranks': ranks,
        'numerical_scope': 'Lower-genus values are shared Lean algorithm outputs. Graph contraction, signed pullback and rational substitution are independently compared.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-input', type=Path, required=True)
    parser.add_argument('--lean-source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='surface-l24-sage-') as cache:
        for variable, name in (('DOT_SAGE', 'sage'), ('ADMCYCLES_CACHE_DIR', 'admcycles'),
                               ('MPLCONFIGDIR', 'matplotlib'), ('XDG_CACHE_HOME', 'xdg')):
            path = Path(cache) / name
            path.mkdir()
            os.environ[variable] = str(path)
        (Path(os.environ['DOT_SAGE']) / 'admcycles').mkdir()
        report = explore(args.lean_input.read_bytes(), args.lean_source.read_bytes())
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'cases': len(report['cases']), 'mutations': len(report['mutations_rejected']),
                      'output': str(args.output)}))


if __name__ == '__main__':
    main()
