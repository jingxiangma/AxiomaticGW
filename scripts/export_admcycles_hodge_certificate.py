#!/usr/bin/env python3
"""Export raw Hodge-packet syntax certificates in the existing Lean strata module.

This is a pure-Python syntax adapter, not a Hodge/GW/CohFT certificate. The
emitted proofs check finite graph validity, the recorded decoration degree,
and membership of each rational expression in the existing homogeneous
strata submodule. No equality to lambda classes or geometric product occurs.
No Sage, admcycles, native_decide, graph search or relation search is used.
"""

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
REPOSITORY = Path(__file__).resolve().parents[1]
RAW_EXPORTER = REPOSITORY / 'scripts/export_admcycles_hodge_strata.py'
RAW_EXPORTER_SHA256 = 'd17ea106eb0f4ae3b52c8929f205dc55f0c882caa996634ea6158f0dc806436e'
HELPER_SHA256 = '28b9d7b9c81d10ef241f6a7a9082cf29047967ddf03ddf1d4433057b6b8d05f8'
INPUT_SHA256 = '1ec7e5df068bd9edbe896dc5bf6f20f59b0e42e81896d2e4364f11efc0c6ec32'
GRAPH_KEYS = {'genus', 'leg_vertices', 'endpoints', 'kappa', 'leg_psi',
              'half_psi', 'admcycles_halfedge_labels', 'codimension'}
NAMESPACE = 'AxiomaticGW.AdmcyclesHodgeStrataCandidates'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path, name, expected):
    require(digest(path) == expected, f'Changed helper source: {path}')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def dependencies():
    shared = load(REPOSITORY / 'scripts/export_admcycles_certificate.py',
                  'hodge_shared_rational_and_vector', HELPER_SHA256)
    source = load(RAW_EXPORTER, 'hodge_raw_graph_validation', RAW_EXPORTER_SHA256)
    return shared, source


def validate_packet(packet, shared, source):
    """Structural and homogeneous-data validation, without Hodge identification."""
    require(type(packet['schema_version']) is int and packet['schema_version'] == 1,
            'Wrong schema version')
    require(packet['kind'] == 'admcycles.hodge_raw_strata_packet' and
            packet['proof_status'] == 'candidate_strata_representatives',
            'This adapter only emits raw candidate representatives')
    require(packet['moduli'] == {'genus': 2, 'markings': 1,
                                'locus': 'full_stable', 'dimension': 4},
            'Wrong moduli frame')
    require(packet['external_label_map'] == [[1, 0]] and
            packet['normalization'] == 'raw_gluing_pushforward' and
            packet['coefficient_ring'] == 'QQ', 'Wrong label/coefficient convention')
    require(packet['kappa_indices'] == [1, 2, 3, 4] and
            packet['kappa_convention'] == source.KAPPA_CONVENTION and
            packet['degree_components'] == [0, 1, 2, 3, 4],
            'Wrong decoration indexing')
    require(packet['claims'] == {'lean_acceptance': False,
            'geometric_hodge_identification': False, 'gw_class_identification': False,
            'cohft': False}, 'Candidate packet overstates its acceptance')
    require(len(packet['pairs']) == 9, 'Missing ordered pair')
    for pair, expected in zip(packet['pairs'], ((a, b) for a in range(3) for b in range(3))):
        require(pair['lambda_indices'] == list(expected) and
                all(type(k) is int for k in pair['lambda_indices']), 'Wrong pair frame')
        require(type(pair['expected_codimension']) is int and
                pair['expected_codimension'] == sum(expected), 'Wrong pair degree')
        require(len(pair['components']) == 5, 'Missing explicit degree component')
        for component, degree in zip(pair['components'], range(5)):
            require(type(component['codimension']) is int and
                    component['codimension'] == degree, 'Wrong component order')
            require(not component['terms'] or degree == sum(expected),
                    'Terms occur outside the recorded homogeneous component')
            for term in component['terms']:
                require(set(term) == {'coefficient', 'graph'}, 'Unexpected term data')
                q = shared.rational(term['coefficient'])
                require(q != 0 and [q.numerator, q.denominator] == term['coefficient'],
                        'Zero or noncanonical rational coefficient')
                graph = term['graph']
                require(set(graph) == GRAPH_KEYS, 'Unexpected graph data')
                source.validate_graph(graph)
                require(graph['codimension'] == degree, 'Decoration degree mismatch')
    return packet


def graph_key(graph):
    # Source halfedge integers are provenance; their order remains the Fin edge/Fin2 order.
    # All mathematical incidence and decoration data are included; no iso test is used.
    return json.dumps({k: v for k, v in graph.items()
                       if k != 'admcycles_halfedge_labels'}, sort_keys=True,
                      separators=(',', ':'))


def incidence_key(graph):
    return json.dumps({k: graph[k] for k in ['genus', 'leg_vertices', 'endpoints']},
                      sort_keys=True, separators=(',', ':'))


def incidence_source(index, graph, shared):
    """Share exact raw incidence tuples, without identification by graph isomorphism."""
    name = f'rawIncidence{index}'
    v, e = len(graph['genus']), len(graph['endpoints'])
    vector = shared.vector
    nested = lambda rows: vector([vector([str(x) for x in row]) for row in rows])
    return '\n'.join([
        f'/-- Raw incidence and vertex genera for explicit incidence encoding {index}. -/',
        f'def {name}Candidate : StableGraphCode.Candidate (Fin 1) {v} {e} where',
        f"  legVertex := {vector([str(x) for x in graph['leg_vertices']])}",
        f"  endpoint := {nested(graph['endpoints'])}",
        f"  genus := {vector([str(x) for x in graph['genus']])}", '',
        '/-- Finite graph validity is checked by kernel reduction, not a source assertion. -/',
        f'theorem {name}Valid : {name}Candidate.Valid 2 := by decide +kernel', '',
    ])


def graph_source(index, graph, shared, incidence_index):
    """The existing Candidate/toDecoration emitter pattern at arity1/kappa bound4."""
    name = f'rawGraph{index}'
    incidence = f'rawIncidence{incidence_index}'
    v, e = len(graph['genus']), len(graph['endpoints'])
    vector = shared.vector
    nested = lambda rows: vector([vector([str(x) for x in row]) for row in rows])
    return '\n'.join([
        '/-- All recorded kappa1..4, external psi and ordered node-branch powers. -/',
        f'def {name}Exponents :',
        f'    DecoratedStableGraph.DecorationIndex (Fin 1) {v} {e} 4 → ℕ',
        '  | .inl (vertex, index) =>',
        f"      ({nested(graph['kappa'])} : Fin {v} → Fin 4 → ℕ) vertex index",
        f"  | .inr (.inl label) => ({vector([str(x) for x in graph['leg_psi']])}) label",
        ('  | .inr (.inr (edge, branch)) =>' if e else
         '  | .inr (.inr (edge, _)) => Fin.elim0 edge'),
        *([f"      ({nested(graph['half_psi'])}) edge branch"] if e else []), '',
        '/-- This representative uses the existing decorated-graph isomorphism quotient. -/',
        f'def {name} : TautologicalStratum 2 (Fin 1) :=',
        '  .mk', '    (DecoratedStableGraph.toDecoration',
        f'      {incidence}Candidate {incidence}Valid {name}Exponents)',
        '    (DecoratedStableGraph.toDecoration_totalGenus',
        f'      {incidence}Candidate {incidence}Valid {name}Exponents)', '',
        '/-- The recorded degree counts edges, positive-index kappa powers and every psi power. -/',
        f"theorem {name}Codimension : {name}.codimension = {graph['codimension']} := by",
        f'  rw [{name}, TautologicalStratum.codimension_mk,',
        '    DecoratedStableGraph.toDecoration_codimension]',
        '  decide +kernel', '',
    ])


def long_vector(items):
    if not items:
        return '  Fin.elim0'
    return '  ![' + ',\n    '.join(items) + ']'


def component_source(a, b, degree, terms, indices, shared):
    name = f'raw_{a}_{b}_degree{degree}'
    n = len(terms)
    column_names = [f'rawGraph{indices[graph_key(t["graph"])]}' for t in terms]
    coordinate_text = [shared.rational_text(shared.rational(t['coefficient'])) for t in terms]
    proofs = (['  intro i', '  exact Fin.elim0 i'] if n == 0 else
              ['  intro i', '  fin_cases i'] +
              [f'  · exact rawGraph{indices[graph_key(t["graph"])]}Codimension' for t in terms])
    return '\n'.join([
        f'/-- Raw source columns for ordered pair ({a},{b}), degree {degree}; repetitions remain. -/',
        f'def {name}Columns : Fin {n} → TautologicalStratum 2 (Fin 1) :=',
        long_vector(column_names), '',
        '/-- Exact raw-gluing coefficients, without an additional automorphism division. -/',
        f'def {name}Coordinates : RelationCertificate.Coordinates {n} :=',
        long_vector(coordinate_text), '',
        '/-- Every source column has the recorded edge-plus-decoration degree. -/',
        f'theorem {name}ColumnsCodimension :',
        f'    ∀ i, ({name}Columns i).codimension = {degree} := by',
        *proofs, '',
        '/-- Formal raw representative only; its name does not identify a geometric Hodge class. -/',
        f'noncomputable def {name} : StrataModule 2 (Fin 1) :=',
        f'  RelationCertificate.interpret {name}Columns {name}Coordinates', '',
        '/-- Homogeneity in the existing free rational strata module. -/',
        f'theorem {name}_mem_degree : {name} ∈ StrataModule.degree {degree} :=',
        '  RelationCertificate.interpret_mem_degree',
        f'    {name}Columns {name}ColumnsCodimension {name}Coordinates', '',
    ])


def emit(packet, shared, input_sha256=INPUT_SHA256):
    indices, graphs, mappings = {}, [], []
    incidence_indices, incidences, graph_incidence_indices = {}, [], []
    for pair in packet['pairs']:
        a, b = pair['lambda_indices']
        for component in pair['components']:
            d = component['codimension']
            for term_index, term in enumerate(component['terms']):
                graph = term['graph']
                key = graph_key(graph)
                if key not in indices:
                    indices[key] = len(graphs)
                    graphs.append(graph)
                    incidence = incidence_key(graph)
                    if incidence not in incidence_indices:
                        incidence_indices[incidence] = len(incidences)
                        incidences.append(graph)
                    graph_incidence_indices.append(incidence_indices[incidence])
                mappings.append({'pair': [a, b], 'degree': d, 'term': term_index,
                                 'graph_declaration': f'rawGraph{indices[key]}',
                                 'incidence_declaration': f'rawIncidence{graph_incidence_indices[indices[key]]}',
                                 'coefficient': term['coefficient'],
                                 'source_halfedge_labels': graph['admcycles_halfedge_labels']})
    prefix = [
        '/-', 'Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA', '-/', 'module', '',
        'public import AxiomaticGW.Tautological.GraphEnumeration',
        'public import AxiomaticGW.Tautological.RelationCertificate', '',
        '/-!', '# Candidate raw admcycles Hodge-packet representatives', '',
        f'Input SHA256: {input_sha256}',
        'The digest records provenance only. Source marking1 labels Lean Fin1 index0.',
        'Source numeric internal flag names are replaced by their ordered Fin edge × Fin2 labels.',
        'No automorphism factor or graph-isomorphism canonicalization is added.',
        'Graph validity and formal homogeneity are the only acceptance claims in this file.',
        'GRR/Chern-class identification, geometric product, constant-map GW and CohFT laws',
        'remain unproved. No relation quotient or geometric realization is asserted.', '-/', '',
        '@[expose] public section', '',
        '-- Long finite vectors require a larger local elaboration recursion bound.',
        '-- Serial theorem elaboration bounds memory; these options change no data or claims.',
        'set_option maxRecDepth 4000', 'set_option Elab.async false', '',
        f'namespace {NAMESPACE}', '',
    ]
    pieces = prefix + [incidence_source(i, graph, shared) for i, graph in enumerate(incidences)]
    pieces += [graph_source(i, graph, shared, graph_incidence_indices[i])
               for i, graph in enumerate(graphs)]
    for pair in packet['pairs']:
        a, b = pair['lambda_indices']
        pieces.extend(component_source(a, b, c['codimension'], c['terms'], indices, shared)
                      for c in pair['components'])
    pieces += [f'end {NAMESPACE}', '']
    return '\n'.join(pieces), graphs, incidences, mappings


def consumer_source():
    return '\n'.join([
        'module', '',
        'public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates', '',
        '@[expose] public section', '',
        'namespace AxiomaticGWTest.AdmcyclesHodgeStrataCandidates', '',
        'open AxiomaticGW', 'open AxiomaticGW.AdmcyclesHodgeStrataCandidates', '',
        '/-- The highest nonempty component uses all node/kappa/psi degree accounting. -/',
        'theorem raw_top_degree : raw_2_2_degree4 ∈ StrataModule.degree 4 :=',
        '  raw_2_2_degree4_mem_degree', '',
        '/-- Both ordered mixed representatives are retained independently. -/',
        'theorem ordered_mixed_degrees :',
        '    raw_1_2_degree3 ∈ StrataModule.degree 3 ∧',
        '      raw_2_1_degree3 ∈ StrataModule.degree 3 :=',
        '  ⟨raw_1_2_degree3_mem_degree, raw_2_1_degree3_mem_degree⟩', '',
        '/-- An explicit empty degree component is the zero formal expression. -/',
        'theorem empty_component_zero : raw_0_0_degree4 = 0 := by',
        '  rw [raw_0_0_degree4, RelationCertificate.interpret_apply]',
        '  exact Fin.sum_univ_zero _', '',
        '/-- The empty component remains in its recorded degree subspace. -/',
        'theorem empty_component_degree : raw_0_0_degree4 ∈ StrataModule.degree 4 :=',
        '  raw_0_0_degree4_mem_degree', '',
        '/-- The degree-zero input is a stable genus-two marked vertex. -/',
        'theorem degree_zero_column_valid : rawIncidence0Candidate.Valid 2 := rawIncidence0Valid', '',
        'end AxiomaticGWTest.AdmcyclesHodgeStrataCandidates', '',
    ])


def mutation_checks(packet, shared, source):
    mutations = []
    q = copy.deepcopy(packet); q['pairs'].pop(); mutations.append(('missing_pair', q))
    q = copy.deepcopy(packet); q['pairs'][0]['components'].pop()
    mutations.append(('missing_zero_component', q))
    q = copy.deepcopy(packet); q['claims']['geometric_hodge_identification'] = True
    mutations.append(('overclaimed_geometric_identification', q))
    q = copy.deepcopy(packet); q['pairs'][0]['components'][0]['terms'][0]['coefficient'][1] = 0
    mutations.append(('zero_denominator', q))
    q = copy.deepcopy(packet); q['pairs'][0]['components'][0]['terms'][0]['graph']['leg_psi'][0] = 1
    mutations.append(('incorrect_decoration_degree', q))
    q = copy.deepcopy(packet); q['normalization'] = 'divide_by_automorphisms'
    mutations.append(('unrequested_automorphism_division', q))
    q = copy.deepcopy(packet); q['pairs'][0]['components'][0]['terms'][0]['graph']['genus'][0] = 1
    mutations.append(('wrong_total_genus', q))
    results = []
    for label, mutated in mutations:
        try:
            validate_packet(mutated, shared, source)
        except (ValueError, KeyError, TypeError):
            results.append({'mutation': label, 'rejected': True})
        else:
            raise ValueError(f'Semantic-data mutation accepted: {label}')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--input-sha256', default=INPUT_SHA256,
                        help='Expected reviewed input digest; defaults to the frozen packet')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tests', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    args = parser.parse_args()
    require(len(args.input_sha256) == 64 and
            all(c in '0123456789abcdef' for c in args.input_sha256),
            'The expected input digest must be lowercase SHA256')
    require(digest(args.input) == args.input_sha256, 'The reviewed raw packet pin changed')
    require(len({p.resolve() for p in [args.output, args.tests, args.ledger]}) == 3,
            'Source, test and ledger outputs must be different files')
    require(all(not p.exists() for p in [args.output, args.tests, args.ledger]),
            'Refusing to replace an existing output')
    shared, source = dependencies()
    packet = json.loads(args.input.read_text(), object_pairs_hook=shared.unique_object)
    validate_packet(packet, shared, source)
    text, graphs, incidences, mappings = emit(packet, shared, args.input_sha256)
    with args.output.open('x') as output:
        output.write(text)
    with args.tests.open('x') as output:
        output.write(consumer_source())
    ledger = {
        'kind': 'axiomatic_gw.hodge_raw_strata_lean_export',
        'status': 'generated_candidate_syntax_uncompiled',
        'input': {'path': str(args.input), 'sha256': digest(args.input)},
        'exporter': {'path': str(Path(__file__)), 'sha256': digest(Path(__file__))},
        'shared_helpers': [
            {'path': str(REPOSITORY / 'scripts/export_admcycles_certificate.py'),
             'sha256': HELPER_SHA256, 'used': ['unique_object', 'rational', 'vector', 'rational_text']},
            {'path': str(RAW_EXPORTER), 'sha256': RAW_EXPORTER_SHA256,
             'used': ['validate_graph', 'KAPPA_CONVENTION']},
        ],
        'proposed_destination':
            'AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataCandidates.lean',
        'source': {'path': str(args.output), 'sha256': digest(args.output),
                   'lines': len(text.splitlines())},
        'tests': {'path': str(args.tests), 'sha256': digest(args.tests)},
        'ordered_pairs': 9, 'explicit_components': 45, 'raw_terms': len(mappings),
        'exact_graph_declarations': len(graphs),
        'exact_incidence_declarations': len(incidences),
        'column_sharing': 'exact mathematical incidence/decoration tuple; numeric source flag names '
                          'encoded as ordered edge/branch positions; source names retained per occurrence; '
                          'no graph isomorphism search',
        'raw_term_to_declaration': mappings,
        'python_mutation_checks': mutation_checks(packet, shared, source),
        'lean_validation': {'run': False, 'axiom_audit_run': False,
                            'reason': 'This pure-Python exporter does not invoke Lean'},
        'accepted_geometric_claims': [],
        'semantic_boundary': 'Free rational strata representatives plus proposed graph/degree replay; '
                             'not lambda, product, constant-map, GW or CohFT identification',
        'next_geometric_obligation': 'Identify realized lambda1/lambda2 through the Hodge-bundle '
                                    'GRR/Chern formula with raw gluing normalization and the '
                                    'kappa convention; then prove product/common-refinement compatibility',
    }
    with args.ledger.open('x') as output:
        output.write(json.dumps(ledger, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: ledger[k] for k in ['status', 'ordered_pairs',
          'explicit_components', 'raw_terms', 'exact_graph_declarations',
          'exact_incidence_declarations', 'source', 'tests']},
          sort_keys=True))


if __name__ == '__main__':
    main()
