#!/usr/bin/env python3
"""Export exact finite raw-strata equality; no Hodge identification or geometry.

The actual previously decoded 122/108 source columns and rational coordinates
are referenced, rather than redefined. Every selected column representative is
bound to those declarations by a finite decorated-graph isomorphism check.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

sys.dont_write_bytecode = True
REPOSITORY = Path(__file__).resolve().parents[1]
NAMESPACE = 'AxiomaticGW.AdmcyclesHodgeStrataIsomorphisms'
RAW = REPOSITORY / 'environments/admcycles-hodge-strata-candidates.json'
RAW_SHA = '1ec7e5df068bd9edbe896dc5bf6f20f59b0e42e81896d2e4364f11efc0c6ec32'
RAW_VALUE_DIGEST = '22c4f504e440270f1fc3592dddbde32b4b5a050203ce0339ccbfe381c8f6159e'
WITNESS = REPOSITORY / 'environments/admcycles-hodge-strata-isomorphism-witness.json'
WITNESS_SHA = '04896b6d8492352593c7281ca2433bef43de2b9960cc14fe6e4700d4f1d3d0db'
DECODER = REPOSITORY / 'scripts/export_admcycles_hodge_certificate.py'
DECODER_SHA = '78697c31d8b9336984c79d78066f87c4fe90743db9828fed90a7ce480ef5895d'
RAW_LEAN = REPOSITORY / 'AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataCandidates.lean'
RAW_LEAN_SHA = '423a3b07dc5bf612d824472708ad0cf79a5f445f5280a4ad0f649958770d83ed'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def load(path, expected, name):
    require(pin(path)['sha256'] == expected, f'Changed reviewed input: {path}')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# Replay the held witness only. No graph search or representative selection is run.
def term(packet, ref):
    require(set(ref) == {'pair_index', 'component_index', 'term_index'} and
        all(type(v) is int and v >= 0 for v in ref.values()), 'Invalid source reference')
    require(ref['pair_index'] in [5, 7] and ref['component_index'] == 3,
        'Source reference leaves the two fixed degree-three products')
    terms = packet['pairs'][ref['pair_index']]['components'][3]['terms']
    require(ref['term_index'] < len(terms), 'Source term reference out of bounds')
    return terms[ref['term_index']]

def hint_valid(G, H, h):
    """Independent exact analogue of GraphIsomorphismHint.Valid preservation tests."""
    n, m = len(G['genus']), len(G['endpoints'])
    require(n == len(H['genus']) and m == len(H['endpoints']), 'Graph sizes differ')
    require(set(h) == {'vertices', 'edges', 'swaps'}, 'Unknown hint field')
    vp, ep, swaps = h['vertices'], h['edges'], h['swaps']
    require(all(type(x) is int for x in vp + ep) and
        sorted(vp) == list(range(n)) and sorted(ep) == list(range(m)) and
        len(swaps) == m and all(type(x) is bool for x in swaps), 'Hint is not finite bijections')
    require(G['leg_psi'] == H['leg_psi'] and len(G['leg_vertices']) == 1 and
        [vp[v] for v in G['leg_vertices']] == H['leg_vertices'], 'External label or psi changed')
    for v in range(n):
        require(G['genus'][v] == H['genus'][vp[v]] and
            G['kappa'][v] == H['kappa'][vp[v]], 'Genus or full kappa powers changed')
    for e in range(m):
        for b in range(2):
            require(vp[G['endpoints'][e][b]] == H['endpoints'][ep[e]][b ^ swaps[e]] and
                G['half_psi'][e][b] == H['half_psi'][ep[e]][b ^ swaps[e]],
                'Node incidence or ordered branch psi changed')
    require(G['codimension'] == H['codimension'] == 3, 'Codimension changed')

def flag_map(G, H, hint):
    # Numeric source names are provenance; Lean uses Fin edge and branch slots.
    return [[1, 1]] + [[G['admcycles_halfedge_labels'][e][b],
        H['admcycles_halfedge_labels'][hint['edges'][e]][b ^ hint['swaps'][e]]]
        for e in range(len(G['endpoints'])) for b in range(2)]

def validate(witness):
    raw = witness['raw_hodge_packet']
    raw_digest = hashlib.sha256(json.dumps(raw, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(raw_digest == witness['raw_hodge_packet_digest'] == RAW_VALUE_DIGEST,
        'Embedded packet differs from the complete pinned raw input')
    require(witness['normalization'] == raw['normalization'] == 'raw_gluing_pushforward',
        'Wrong raw pushforward normalization')
    require(raw['pairs'][5]['lambda_indices'] == [1, 2] and
        raw['pairs'][7]['lambda_indices'] == [2, 1], 'Fixed ordered products changed')
    expected = [(i, j) for i in [5, 7] for j in
        range(len(raw['pairs'][i]['components'][3]['terms']))]
    mappings = witness['mappings']
    require([(r['source']['pair_index'], r['source']['term_index']) for r in mappings] == expected,
        'Mapping omits, reorders or duplicates a raw occurrence')
    representatives = witness['representatives']
    sums = [[Fraction(0), Fraction(0)] for _ in representatives]
    for record in mappings:
        index = record['representative_index']
        require(type(index) is int and 0 <= index < len(representatives), 'Bad representative index')
        source = term(raw, record['source'])
        target = term(raw, representatives[index]['source_reference'])
        hint_valid(source['graph'], target['graph'], record['hint'])
        require(record['admcycles_flag_map'] == flag_map(source['graph'], target['graph'], record['hint']),
            'Source flag provenance map changed')
        require(record['coefficient'] == source['coefficient'], 'Raw source coefficient changed')
        n, d = source['coefficient']
        q = Fraction(n, d)
        require([q.numerator, q.denominator] == source['coefficient'] and q != 0,
            'Source rational is not normalized')
        sums[index][0 if record['source']['pair_index'] == 5 else 1] += q
    for representative, (lhs, rhs) in zip(representatives, sums):
        require(representative['left_coefficient'] == [lhs.numerator, lhs.denominator] and
            representative['right_coefficient'] == [rhs.numerator, rhs.denominator],
            'Recorded grouped coordinates changed')
        require(lhs == rhs and representative['difference'] == [0, 1],
            'The two products have a nonzero grouped difference')
    require(not any(name == 'sage' or name.startswith('sage.') or name == 'admcycles' or
        name.startswith('admcycles.') for name in sys.modules), 'Heavy runtime imported')
    return {'raw_occurrences_checked': len(mappings), 'representatives': len(representatives),
        'nonzero_grouped_coordinates': sum(x[0] != 0 for x in sums),
        'exact_grouped_difference': 0, 'all_hint_preservation_checks': True,
        'all_source_flags_and_coefficients_retained': True}


def list_text(xs):
    return '[' + ', '.join(str(x).lower() for x in xs) + ']'


def vector_text(xs):
    return '  ![' + ',\n    '.join(str(x) for x in xs) + ']'


def emit(witness, decoder, shared, mappings):
    source = [
        '/-', 'Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA', '-/', 'module', '',
        'public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataCandidates',
        'public import AxiomaticGW.Tautological.GraphIsomorphismHint', '',
        '/-!', '# Exact isomorphism regrouping of two raw strata expressions', '',
        f'Witness SHA256: {WITNESS_SHA}',
        f'Decoded source SHA256: {RAW_LEAN_SHA}',
        'The digests record provenance; the proofs reference the actual source definitions.',
        'All 122/108 source occurrences and their exact coefficients are retained.',
        'Only decorated graph isomorphisms and rational addition are used.',
        'This proves equality in the free strata module. It does not identify Hodge',
        'classes, certify a geometric product, or assert CohFT/GW compatibility.', '-/', '',
        '@[expose] public section', '',
        'set_option maxRecDepth 4000', 'set_option Elab.async false', '',
        f'namespace {NAMESPACE}', '',
        'open scoped BigOperators', 'open AdmcyclesHodgeStrataCandidates', '',
    ]
    lookup = {(tuple(m['pair']), m['degree'], m['term']): m for m in mappings}

    def mapped(ref):
        pair = witness['raw_hodge_packet']['pairs'][ref['pair_index']]['lambda_indices']
        return lookup[(tuple(pair), ref['component_index'], ref['term_index'])]

    reps = [mapped(r['source_reference']) for r in witness['representatives']]
    source.extend([
        '/-- Fixed representatives are selected actual raw source columns. -/',
        'def representatives : Fin 44 → TautologicalStratum 2 (Fin 1) :=',
        vector_text([r['graph_declaration'] for r in reps]), '',
        '/-- Exact collected coefficients in this fixed representative frame. -/',
        'def collectedCoordinates : RelationCertificate.Coordinates 44 :=',
        vector_text([shared.rational_text(shared.rational(r['left_coefficient']))
                     for r in witness['representatives']]), '',
    ])
    proofs, bindings, audit = {}, [], []
    for record in witness['mappings']:
        original = mapped(record['source'])
        representative = reps[record['representative_index']]
        key = (original['graph_declaration'], representative['graph_declaration'])
        if key not in proofs:
            n = len(proofs)
            hint, theorem = f'rawHint{n}', f'rawGraphIso{n}'
            proofs[key] = theorem
            G, H = [m['graph_declaration'] for m in [original, representative]]
            I, J = [m['incidence_declaration'] for m in [original, representative]]
            h = record['hint']
            # An identity hint must still identify its independently indexed witness representative.
            rhs = f"representatives {record['representative_index']}" if G == H else H
            source.extend([
                '/-- Proposed finite vertex, edge and ordered branch maps. -/',
                f'def {hint} : GraphIsomorphismHint where',
                f"  vertices := {list_text(h['vertices'])}",
                f"  edges := {list_text(h['edges'])}",
                f"  swaps := {list_text(h['swaps'])}", '',
                '/-- A checked decorated isomorphism identifies these actual source strata. -/',
                f'theorem {theorem} : {G} = {rhs} :=',
                '  TautologicalStratum.mk_eq_mk_of_isomorphic?',
                '    (DecoratedStableGraph.toDecoration_totalGenus',
                f'      {I}Candidate {I}Valid {G}Exponents)',
                '    (DecoratedStableGraph.toDecoration_totalGenus',
                f'      {J}Candidate {J}Valid {H}Exponents)',
                f'    (GraphIsomorphismHint.check_sound {hint} _ _',
                '      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))', '',
            ])
            audit.append(f'{NAMESPACE}.{theorem}')
        bindings.append({**record, 'source_graph': original['graph_declaration'],
                         'representative_graph': representative['graph_declaration'],
                         'isomorphism_theorem': proofs[key]})
    for a, b in [(1, 2), (2, 1)]:
        selected = [record for record in bindings
                    if witness['raw_hodge_packet']['pairs'][record['source']['pair_index']]
                    ['lambda_indices'] == [a, b]]
        count = len(selected)
        name = f'raw{a}{b}Degree3'
        index = f'index_{a}_{b}'
        source.extend([
            '/-- Every occurrence selects one fixed representative; no term is dropped. -/',
            f'def {index} : Fin {count} → Fin 44 :=',
            vector_text([r['representative_index'] for r in selected]), '',
            '/-- Every lookup is bound to the complete previously decoded column vector. -/',
            f'theorem columns_{a}_{b}_eq :',
            f'    ∀ i, {name}Columns i = representatives ({index} i) := by',
            '  intro i', '  fin_cases i',
            *[f"  · exact {r['isomorphism_theorem']}" for r in selected], '',
            '/-- All coefficients from the actual input coordinate vector, with repetitions. -/',
            f'def grouped_{a}_{b} : RelationCertificate.Coordinates 44 :=',
            f'  ∑ i, Pi.single ({index} i) ({name}Coordinates i)', '',
            '/-- Exact rational sums agree at every one of the 44 held coordinates. -/',
            f'theorem grouped_{a}_{b}_eq : grouped_{a}_{b} = collectedCoordinates := by',
            '  funext i', '  fin_cases i <;> decide +kernel', '',
        ])
        audit.extend(f'{NAMESPACE}.{n}' for n in
                     [f'columns_{a}_{b}_eq', f'grouped_{a}_{b}_eq'])
    source.extend([
        '/-- Repeated isomorphic columns regroup by linearity in the existing free module. -/',
        'theorem interpret_grouped {m n : ℕ}',
        '    (columns : Fin m → TautologicalStratum 2 (Fin 1))',
        '    (frame : Fin n → TautologicalStratum 2 (Fin 1))',
        '    (index : Fin m → Fin n) (coordinates : RelationCertificate.Coordinates m)',
        '    (hc : ∀ i, columns i = frame (index i)) :',
        '    RelationCertificate.interpret columns coordinates =',
        '      RelationCertificate.interpret frame',
        '        (∑ i, Pi.single (index i) (coordinates i)) := by',
        '  classical',
        '  calc',
        '    RelationCertificate.interpret columns coordinates =',
        '        ∑ i, coordinates i • StrataModule.basis (columns i) := rfl',
        '    _ = ∑ i, coordinates i • StrataModule.basis (frame (index i)) := by',
        '      apply Finset.sum_congr rfl',
        '      intro i _', '      rw [hc i]',
        '    _ = RelationCertificate.interpret frame',
        '        (∑ i, Pi.single (index i) (coordinates i)) := by',
        '      simp only [map_sum, RelationCertificate.interpret,',
        '        Fintype.linearCombination_apply_single]', '',
        '/-- The first complete raw expression has the certified collected coordinates. -/',
        'theorem raw_1_2_eq_collected : raw12Degree3 =',
        '    RelationCertificate.interpret representatives collectedCoordinates := by',
        '  calc',
        '    raw12Degree3 = RelationCertificate.interpret representatives grouped_1_2 :=',
        '      interpret_grouped _ _ _ _ columns_1_2_eq',
        '    _ = _ := congrArg (RelationCertificate.interpret representatives) grouped_1_2_eq', '',
        '/-- The second complete raw expression has the same certified coordinates. -/',
        'theorem raw_2_1_eq_collected : raw21Degree3 =',
        '    RelationCertificate.interpret representatives collectedCoordinates := by',
        '  calc',
        '    raw21Degree3 = RelationCertificate.interpret representatives grouped_2_1 :=',
        '      interpret_grouped _ _ _ _ columns_2_1_eq',
        '    _ = _ := congrArg (RelationCertificate.interpret representatives) grouped_2_1_eq', '',
        '/-- These two actual finite raw sums agree before imposing tautological relations. -/',
        'theorem raw_ordered_degree3_equal : raw12Degree3 = raw21Degree3 :=',
        '  raw_1_2_eq_collected.trans raw_2_1_eq_collected.symm', '',
        f'end {NAMESPACE}', '',
    ])
    audit.extend(f'{NAMESPACE}.{n}' for n in ['interpret_grouped',
        'raw_1_2_eq_collected', 'raw_2_1_eq_collected', 'raw_ordered_degree3_equal'])
    return '\n'.join(source), bindings, audit


def consumer_source():
    return '\n'.join([
        'module', '',
        'public import AxiomaticGW.GKM.Fixtures.AdmcyclesHodgeStrataIsomorphisms', '',
        '@[expose] public section', '',
        'namespace AxiomaticGWTest.AdmcyclesHodgeStrataIsomorphisms', '',
        'open AxiomaticGW', 'open AxiomaticGW.AdmcyclesHodgeStrataCandidates',
        'open AxiomaticGW.AdmcyclesHodgeStrataIsomorphisms', '',
        '/-- Public consumers get equality of the exact two decoded raw expressions. -/',
        'theorem exact_raw_inputs_equal : raw12Degree3 = raw21Degree3 :=',
        '  raw_ordered_degree3_equal', '',
        '/-- The common expression remains in degree three of the free strata module. -/',
        'theorem common_expression_degree :',
        '    RelationCertificate.interpret representatives collectedCoordinates ∈',
        '      StrataModule.degree 3 := by',
        '  rw [← raw_1_2_eq_collected]',
        '  exact raw_1_2_degree3_mem_degree', '',
        '/-- The checked equality persists after any given rational linear realization. -/',
        'theorem equality_under_linear_map',
        '    (M : Type) [AddCommGroup M] [Module ℚ M]',
        '    (f : StrataModule 2 (Fin 1) →ₗ[ℚ] M) :',
        '    f raw12Degree3 = f raw21Degree3 :=',
        '  congrArg f raw_ordered_degree3_equal', '',
        'end AxiomaticGWTest.AdmcyclesHodgeStrataIsomorphisms', '',
    ])


def prepare(raw_path=RAW, witness_path=WITNESS, raw_lean_path=RAW_LEAN):
    """Bind the fixed witness to the actual raw packet and decoded public source."""
    require(pin(raw_path)['sha256'] == RAW_SHA, 'Raw packet input changed')
    require(pin(witness_path)['sha256'] == WITNESS_SHA, 'Witness input changed')
    require(pin(raw_lean_path)['sha256'] == RAW_LEAN_SHA, 'Decoded actual Lean source changed')
    decoder = load(DECODER, DECODER_SHA, 'hodge_raw_declaration_decoder')
    shared, raw_helper = decoder.dependencies()
    raw = json.loads(raw_path.read_text(), object_pairs_hook=shared.unique_object)
    witness = json.loads(witness_path.read_text(), object_pairs_hook=shared.unique_object)
    require(raw == witness['raw_hodge_packet'],
            'Witness does not embed the complete actual raw packet')
    checks = validate(witness)
    decoder.validate_packet(raw, shared, raw_helper)
    decoded, graphs, incidences, mappings = decoder.emit(raw, shared)
    require(decoded == raw_lean_path.read_text(), 'Source declaration reconstruction is not exact')
    source, bindings, audit = emit(witness, decoder, shared, mappings)
    require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source),
            'Forbidden placeholder/native acceptance in emitted source')
    require(max(map(len, source.splitlines())) <= 100, 'Generated Lean line exceeds 100 columns')
    audit.extend('AxiomaticGWTest.AdmcyclesHodgeStrataIsomorphisms.' + name for name in
                 ['exact_raw_inputs_equal', 'common_expression_degree', 'equality_under_linear_map'])
    return source, bindings, audit, checks


def main():
    started = time.monotonic()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=RAW, help='Fixed actual raw packet')
    parser.add_argument('--witness', type=Path, default=WITNESS, help='Fixed complete isomorphism witness')
    parser.add_argument('--raw-lean', type=Path, default=RAW_LEAN, help='Actual decoded public Lean module')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tests', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    args = parser.parse_args()
    outputs = [args.output, args.tests, args.ledger]
    require(len({p.resolve() for p in outputs}) == 3, 'Output files must be different')
    require(all(not p.exists() for p in outputs), 'Refusing to replace an existing output')
    source, bindings, audit, checks = prepare(args.input, args.witness, args.raw_lean)
    with args.output.open('x') as output:
        output.write(source)
    with args.tests.open('x') as output:
        output.write(consumer_source())
    ledger = {'status': 'generated_candidate_syntax_uncompiled', 'lean_executed': False,
        'producer': pin(Path(__file__)), 'input': pin(args.input), 'witness': pin(args.witness),
        'decoder': pin(DECODER), 'actual_decoded_source': pin(args.raw_lean),
        'source': pin(args.output), 'tests': pin(args.tests),
        'checks': checks, 'exact_raw_source_reproduced': True,
        'occurrences': len(bindings), 'unique_graph_isomorphism_proofs': len(audit) - 11,
        'representatives': 44, 'audit_declarations': len(audit), 'audit_names': audit,
        'occurrence_to_actual_declarations': bindings,
        'source_lines': len(source.splitlines()),
        'elapsed_seconds': round(time.monotonic() - started, 6),
        'mathematical_scope': 'Equality of the existing raw12Degree3 and raw21Degree3 '
            'in StrataModule 2 (Fin 1), by finite decorated graph isomorphisms and rational '
            'addition; no Hodge identification, geometric product or CohFT/GW theorem'}
    with args.ledger.open('x') as output:
        output.write(json.dumps(ledger, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in ledger.items()
                      if k not in ['occurrence_to_actual_declarations', 'audit_names']}, sort_keys=True))


if __name__ == '__main__':
    main()
