#!/usr/bin/env python3
"""Replay one fixed equality of actual raw degree-two strata expressions.

All 28/16 occurrences, rational coefficients and oriented graph decorations
are retained. No graph search, Sage, admcycles, product or Hodge identification
is performed. Existing source pins are checked before importing any helper.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
RAW = 'environments/admcycles-hodge-strata-candidates.json'
WITNESS = 'environments/admcycles-hodge-degree-two-witness.json'
RAW_LEAN = 'AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataCandidates.lean'
ISO_LEAN = 'AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataIsomorphisms.lean'
ASSEMBLY = 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroRawAssembly.lean'
DECODER = 'scripts/export_admcycles_hodge_certificate.py'
PINS = {
    RAW: '1ec7e5df068bd9edbe896dc5bf6f20f59b0e42e81896d2e4364f11efc0c6ec32',
    RAW_LEAN: '423a3b07dc5bf612d824472708ad0cf79a5f445f5280a4ad0f649958770d83ed',
    ISO_LEAN: 'deeb0b19889b266faddfac1fce8981ca7ccda04bb220806d10459571116389fc',
    ASSEMBLY: 'b0c2ebe480c81ee7288b302e3cfcbac6f10778caf4765eb6770c6d3a37fcfa51',
    DECODER: '78697c31d8b9336984c79d78066f87c4fe90743db9828fed90a7ce480ef5895d',
}
WITNESS_SHA = 'a68d166f6b3063ac4295b8104304e0644f2caca47d6f1a869a5d846fb591cef1'
NS = 'AxiomaticGW.GKM.HodgeDegreeTwoRawRelation'
TEST_NS = 'AxiomaticGWTest.HodgeDegreeTwoRawRelation'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pin(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def load(path, expected, name):
    require(pin(path)['sha256'] == expected, f'Changed reviewed helper before execution: {path}')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, f'Duplicate JSON key: {key}')
        out[key] = value
    return out


def term(raw, ref):
    require(set(ref) == {'pair_index', 'component_index', 'term_index'} and
        all(type(v) is int and v >= 0 for v in ref.values()), 'Invalid source reference')
    require(ref['pair_index'] in [4, 2] and ref['component_index'] == 2,
        'Source reference leaves the two actual degree-two components')
    terms = raw['pairs'][ref['pair_index']]['components'][2]['terms']
    require(ref['term_index'] < len(terms), 'Out-of-range source occurrence')
    return terms[ref['term_index']]


def hint_valid(G, H, h):
    n, m = len(G['genus']), len(G['endpoints'])
    require(n == len(H['genus']) and m == len(H['endpoints']), 'Graph sizes differ')
    require(set(h) == {'vertices', 'edges', 'swaps'}, 'Unknown hint field')
    vp, ep, swaps = h['vertices'], h['edges'], h['swaps']
    require(all(type(x) is int for x in vp + ep) and
        sorted(vp) == list(range(n)) and sorted(ep) == list(range(m)) and
        len(swaps) == m and all(type(x) is bool for x in swaps), 'Hint is not bijective')
    require(G['leg_psi'] == H['leg_psi'] and len(G['leg_vertices']) == 1 and
        [vp[v] for v in G['leg_vertices']] == H['leg_vertices'], 'External label or psi changed')
    for v in range(n):
        require(G['genus'][v] == H['genus'][vp[v]] and
            G['kappa'][v] == H['kappa'][vp[v]], 'Genus or kappa decoration changed')
    for e in range(m):
        for b in range(2):
            require(vp[G['endpoints'][e][b]] == H['endpoints'][ep[e]][b ^ swaps[e]] and
                G['half_psi'][e][b] == H['half_psi'][ep[e]][b ^ swaps[e]],
                'Node incidence or ordered branch psi changed')
    require(G['codimension'] == H['codimension'] == 2, 'Codimension changed')


def flag_map(G, H, h):
    return [[1, 1]] + [[G['admcycles_halfedge_labels'][e][b],
        H['admcycles_halfedge_labels'][h['edges'][e]][b ^ h['swaps'][e]]]
        for e in range(len(G['endpoints'])) for b in range(2)]


def validate(raw, w):
    require(w['schema_version'] == 1 and
        w['kind'] == 'fixed_raw_degree_two_isomorphism_witness', 'Wrong witness kind')
    require(w['raw_packet_sha256'] == PINS[RAW], 'Witness raw source pin changed')
    require(w['normalization'] == raw['normalization'] == 'raw_gluing_pushforward',
        'Raw gluing convention changed')
    require(w['pair_indices'] == [4, 2] and w['component_index'] == 2 and
        w['right_multiplier'] == [2, 1], 'The fixed requested identity changed')
    require(w['claims'] == {'lean_acceptance': False, 'geometric_hodge_identification': False,
        'geometric_mumford_relation': False, 'gw_or_cohft': False}, 'Witness overstates acceptance')
    require(raw['pairs'][4]['lambda_indices'] == [1, 1] and
        raw['pairs'][2]['lambda_indices'] == [0, 2], 'Ordered pair frame changed')
    require([len(raw['pairs'][i]['components'][2]['terms']) for i in [4, 2]] == [28, 16],
        'Actual source occurrence counts changed')
    refs = [{'pair_index': 2, 'component_index': 2, 'term_index': i} for i in range(16)]
    require([r['source_reference'] for r in w['representatives']] == refs,
        'Fixed representative frame changed')
    expected = [{'pair_index': i, 'component_index': 2, 'term_index': j}
                for i, count in [(4, 28), (2, 16)] for j in range(count)]
    require([r['source'] for r in w['mappings']] == expected,
        'An occurrence was omitted, duplicated or reordered')
    sums = [[Fraction(0), Fraction(0)] for _ in refs]
    for r in w['mappings']:
        j = r['representative_index']
        require(type(j) is int and 0 <= j < 16, 'Bad representative index')
        src, dst = term(raw, r['source']), term(raw, refs[j])
        hint_valid(src['graph'], dst['graph'], r['hint'])
        require(r['admcycles_flag_map'] == flag_map(src['graph'], dst['graph'], r['hint']),
            'Source halfedge provenance changed')
        require(r['coefficient'] == src['coefficient'], 'Actual source coefficient changed')
        q = Fraction(*r['coefficient'])
        require(q and [q.numerator, q.denominator] == r['coefficient'], 'Noncanonical rational')
        sums[j][0 if r['source']['pair_index'] == 4 else 1] += q
    for r, (a, b) in zip(w['representatives'], sums):
        require(r['left_coefficient'] == [a.numerator, a.denominator] and
            r['right_coefficient'] == [b.numerator, b.denominator], 'Collected coefficient changed')
        require(a == 2 * b and r['difference'] == [0, 1], 'Requested raw equality fails')
    return {'occurrences': 44, 'left_occurrences': 28, 'right_occurrences': 16,
        'representatives': 16, 'exact_difference': 0, 'all_decorations_and_flags_checked': True}


def vector(xs):
    return '  ![' + ',\n    '.join(str(x) for x in xs) + ']'


def emit(raw, w, shared, mappings):
    lines = ['/-', 'Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA', '-/', 'module', '',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRawAssembly', '',
        '/-!', '# A checked relation between two fixed raw degree-two expressions', '',
        f'Witness SHA256: {WITNESS_SHA}', f'Decoded source SHA256: {PINS[RAW_LEAN]}',
        'All 28/16 actual occurrences and their rational coefficients are retained.',
        'Finite decorated graph isomorphisms and rational linearity prove the equality.',
        'This is not a geometric Mumford relation, a product-realization law, or a',
        'Hodge/GW/CohFT identification. No new realization hypothesis is used.', '-/', '',
        '@[expose] public section', '', 'set_option autoImplicit false',
        'set_option maxRecDepth 4000', 'set_option Elab.async false', '',
        f'namespace {NS}', '', 'open AdmcyclesHodgeStrataCandidates',
        'open EquivariantCoefficients', 'open scoped BigOperators', '',
        'noncomputable section', '', 'attribute [local instance] strataRealizationModule', '']
    lookup = {(tuple(m['pair']), m['degree'], m['term']): m for m in mappings}
    def mapped(ref):
        pair = tuple(raw['pairs'][ref['pair_index']]['lambda_indices'])
        return lookup[(pair, ref['component_index'], ref['term_index'])]
    reps = [mapped(r['source_reference']) for r in w['representatives']]
    lines += ['/-- The frame consists of the sixteen actual raw (0,2) source columns. -/',
        'def representatives : Fin 16 → TautologicalStratum 2 (Fin 1) :=',
        vector([r['graph_declaration'] for r in reps]), '',
        '/-- Exact coefficients of the actual (0,2) expression in this frame. -/',
        'def collectedCoordinates : RelationCertificate.Coordinates 16 :=',
        vector([shared.rational_text(Fraction(*r['right_coefficient']))
                for r in w['representatives']]), '']
    proofs, bindings, audit = {}, [], []
    for r in w['mappings']:
        original, representative = mapped(r['source']), reps[r['representative_index']]
        G, H = original['graph_declaration'], representative['graph_declaration']
        key = (G, H)
        if key not in proofs:
            n = len(proofs); name = f'rawGraphIso{n}'; hname = f'rawHint{n}'
            proofs[key] = name
            I, J = original['incidence_declaration'], representative['incidence_declaration']
            h = r['hint']
            # An identity hint must still identify its independently indexed witness representative.
            rhs = f"representatives {r['representative_index']}" if G == H else H
            txt = lambda x: str(x).lower()
            lines += ['/-- Proposed vertex, edge and ordered-branch bijections. -/',
                f'def {hname} : GraphIsomorphismHint where',
                f"  vertices := {txt(h['vertices'])}", f"  edges := {txt(h['edges'])}",
                f"  swaps := {txt(h['swaps'])}", '',
                '/-- Kernel-checked preservation of every source decoration. -/',
                f'theorem {name} : {G} = {rhs} :=',
                '  TautologicalStratum.mk_eq_mk_of_isomorphic?',
                '    (DecoratedStableGraph.toDecoration_totalGenus',
                f'      {I}Candidate {I}Valid {G}Exponents)',
                '    (DecoratedStableGraph.toDecoration_totalGenus',
                f'      {J}Candidate {J}Valid {H}Exponents)',
                f'    (GraphIsomorphismHint.check_sound {hname} _ _',
                '      (by simp only [DecoratedStableGraph.toDecoration_eq_mk]; decide +kernel))', '']
            audit.append(NS + '.' + name)
        bindings.append({**r, 'source_graph': G, 'representative_graph': H,
            'isomorphism_theorem': proofs[key]})
    for a, b, pair_index in [(1, 1, 4), (0, 2, 2)]:
        selected = [r for r in bindings if r['source']['pair_index'] == pair_index]
        name, index = f'raw{a}{b}Degree2', f'index_{a}_{b}'
        target = '(2 : ℚ) • collectedCoordinates' if pair_index == 4 else 'collectedCoordinates'
        lines += ['/-- One representative lookup for every original occurrence. -/',
            f'def {index} : Fin {len(selected)} → Fin 16 :=',
            vector([r['representative_index'] for r in selected]), '',
            '/-- Bind the full original column vector to checked source isomorphisms. -/',
            f'theorem columns_{a}_{b}_eq :',
            f'    ∀ i, {name}Columns i = representatives ({index} i) := by',
            '  intro i', '  fin_cases i',
            *[f"  · exact {r['isomorphism_theorem']}" for r in selected], '',
            '/-- All actual source coefficients are collected, without dropping repetitions. -/',
            f'def grouped_{a}_{b} : RelationCertificate.Coordinates 16 :=',
            f'  ∑ i, Pi.single ({index} i) ({name}Coordinates i)', '',
            '/-- Exact rational arithmetic in all sixteen coordinates. -/',
            f'theorem grouped_{a}_{b}_eq : grouped_{a}_{b} = {target} := by',
            '  funext i', '  fin_cases i <;> decide +kernel', '',
            '/-- The previously decoded complete raw expression has these coordinates. -/',
            f'theorem raw_{a}_{b}_eq_collected : {name} =',
            f'    RelationCertificate.interpret representatives ({target}) := by',
            '  calc', f'    {name} = RelationCertificate.interpret representatives grouped_{a}_{b} :=',
            '      AdmcyclesHodgeStrataIsomorphisms.interpret_grouped',
            f'        _ _ _ _ columns_{a}_{b}_eq',
            '    _ = _ := congrArg (RelationCertificate.interpret representatives)',
            f'      grouped_{a}_{b}_eq', '']
        audit += [NS + '.' + n for n in [f'columns_{a}_{b}_eq',
            f'grouped_{a}_{b}_eq', f'raw_{a}_{b}_eq_collected']]
    lines += [
        '/-- Equality of these two actual raw expressions, before any relation quotient. -/',
        'theorem raw_degree_two_equal : raw11Degree2 = (2 : ℚ) • raw02Degree2 := by',
        '  rw [raw_1_1_eq_collected, raw_0_2_eq_collected, map_smul]', '',
        '/-- Rational linearity transfers the exact equality to the existing realization. -/',
        'theorem map_raw_degree_two_equal {C : StableCurveCohomology Coefficient}',
        '    (A : StrataRealization C 2 (Fin 1)) :',
        '    A.map raw11Degree2 = (2 : Coefficient) • A.map raw02Degree2 := by',
        '  rw [raw_degree_two_equal, two_smul, map_add, two_smul]', '',
        '/-- The complete plane assembly needs only the original raw unit and (0,2) classes. -/',
        'theorem plane_candidateClass_eq_raw_degree_two',
        '    {C : StableCurveCohomology Coefficient} (A : StrataRealization C 2 (Fin 1)) :',
        '    HodgeDegreeZeroFullCoefficientReplay.Plane.candidateClass A =',
        '      (x ^ 2 - x * y + y ^ 2) • A.map raw00Degree0 +',
        '      (9 : Coefficient) • A.map raw02Degree2 := by',
        '  rw [HodgeDegreeZeroRawAssembly.plane_candidateClass_eq_raw_regular,',
        '    map_raw_degree_two_equal, smul_smul, add_assoc, ← add_smul]',
        '  norm_num only', '',
        '/-- The complete first blowup assembly has one actual degree-two raw expression. -/',
        'theorem oneBlowup_candidateClass_eq_raw_degree_two',
        '    {C : StableCurveCohomology Coefficient} (A : StrataRealization C 2 (Fin 1)) :',
        '    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =',
        '      (8 : Coefficient) • A.map raw02Degree2 := by',
        '  rw [HodgeDegreeZeroRawAssembly.oneBlowup_candidateClass_eq_raw_regular,',
        '    map_raw_degree_two_equal, smul_smul]', '  norm_num only', '',
        '/-- The complete second blowup assembly preserves its signed raw unit term. -/',
        'theorem twoBlowups_candidateClass_eq_raw_degree_two',
        '    {C : StableCurveCohomology Coefficient} (A : StrataRealization C 2 (Fin 1)) :',
        '    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A =',
        '      (-(x ^ 2 - x * y + y ^ 2)) • A.map raw00Degree0 +',
        '      (7 : Coefficient) • A.map raw02Degree2 := by',
        '  rw [HodgeDegreeZeroRawAssembly.twoBlowups_candidateClass_eq_raw_regular,',
        '    map_raw_degree_two_equal, smul_smul, add_assoc, ← add_smul]',
        '  norm_num only', '', 'end', '', f'end {NS}', '']
    audit += [NS + '.' + n for n in ['raw_degree_two_equal', 'map_raw_degree_two_equal',
        'plane_candidateClass_eq_raw_degree_two', 'oneBlowup_candidateClass_eq_raw_degree_two',
        'twoBlowups_candidateClass_eq_raw_degree_two']]
    return '\n'.join(lines), bindings, audit


def consumer_source():
    return '''module

public import AxiomaticGW.GKM.Fixtures.HodgeDegreeTwoRawRelation

@[expose] public section

set_option autoImplicit false

namespace AxiomaticGWTest.HodgeDegreeTwoRawRelation

open AxiomaticGW AxiomaticGW.GKM
open AdmcyclesHodgeStrataCandidates HodgeDegreeTwoRawRelation EquivariantCoefficients

noncomputable section

/-- Any rational linear map preserves the equality of the original complete raw sums. -/
theorem exact_relation_under_linear_map
    (M : Type) [AddCommGroup M] [Module ℚ M]
    (f : StrataModule 2 (Fin 1) →ₗ[ℚ] M) :
    f raw11Degree2 = (2 : ℚ) • f raw02Degree2 := by
  rw [raw_degree_two_equal, map_smul]

/-- The original degree-two expression is retained, rather than replaced by zero. -/
theorem common_expression_degree :
    RelationCertificate.interpret representatives collectedCoordinates ∈
      StrataModule.degree 2 := by
  rw [← raw_0_2_eq_collected]
  exact raw_0_2_degree2_mem_degree

attribute [local instance] strataRealizationModule

/-- The complete fixed-point sum is available without D, hfund, or a product premise. -/
theorem oneBlowup_complete_class {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      (8 : Coefficient) • A.map raw02Degree2 :=
  oneBlowup_candidateClass_eq_raw_degree_two A

/-- The two surfaces differ by the actual unit term and one copy of the degree-two class. -/
theorem blowup_complete_class_difference {C : StableCurveCohomology Coefficient}
    (A : StrataRealization C 2 (Fin 1)) :
    HodgeDegreeZeroFullCoefficientReplay.TwoBlowups.candidateClass A +
      (x ^ 2 - x * y + y ^ 2) • A.map raw00Degree0 -
      HodgeDegreeZeroFullCoefficientReplay.OneBlowup.candidateClass A =
      -A.map raw02Degree2 := by
  rw [twoBlowups_candidateClass_eq_raw_degree_two, oneBlowup_candidateClass_eq_raw_degree_two]
  rw [show (8 : Coefficient) = (7 : Coefficient) + 1 by norm_num only,
    add_smul (7 : Coefficient) 1 (A.map raw02Degree2), one_smul]
  simp only [neg_smul]
  abel

end

end AxiomaticGWTest.HodgeDegreeTwoRawRelation
'''


def prepare(repository=ROOT, witness_path=None, raw_path=None):
    repository = Path(repository)
    witness_path = Path(witness_path) if witness_path else repository / WITNESS
    raw_path = Path(raw_path) if raw_path else repository / RAW
    for rel, expected in PINS.items():
        path = raw_path if rel == RAW else repository / rel
        require(pin(path)['sha256'] == expected, f'Changed reviewed source: {path}')
    require(pin(witness_path)['sha256'] == WITNESS_SHA, 'Changed fixed isomorphism witness')
    # No imported helper is executed before all independent source pins above pass.
    decoder = load(repository / DECODER, PINS[DECODER], 'hodge_degree_two_raw_decoder')
    shared, raw_helper = decoder.dependencies()
    raw = json.loads(raw_path.read_text(), object_pairs_hook=unique_object)
    witness = json.loads(witness_path.read_text(), object_pairs_hook=unique_object)
    checks = validate(raw, witness)
    decoder.validate_packet(raw, shared, raw_helper)
    decoded, _, _, mappings = decoder.emit(raw, shared)
    require(decoded == (repository / RAW_LEAN).read_text(), 'Actual raw Lean source replay differs')
    source, bindings, audit = emit(raw, witness, shared, mappings)
    tests = consumer_source()
    require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source + tests),
        'Forbidden placeholder or native acceptance')
    require(max(map(len, (source + tests).splitlines())) <= 100, 'Generated Lean long line')
    require(not any(n == 'sage' or n.startswith('sage.') or n == 'admcycles' or
        n.startswith('admcycles.') for n in sys.modules), 'Heavy runtime imported')
    audit += [TEST_NS + '.' + n for n in ['exact_relation_under_linear_map',
        'common_expression_degree', 'oneBlowup_complete_class', 'blowup_complete_class_difference']]
    return source, tests, bindings, audit, checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', type=Path, default=ROOT)
    parser.add_argument('--input', type=Path)
    parser.add_argument('--witness', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tests', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    args = parser.parse_args()
    outputs = [args.output, args.tests, args.ledger]
    require(len({p.resolve() for p in outputs}) == 3, 'Output paths collide')
    require(all(not p.exists() for p in outputs), 'Refusing to replace an output')
    source, tests, bindings, audit, checks = prepare(args.repository, args.witness, args.input)
    args.output.write_text(source); args.tests.write_text(tests)
    ledger = {'status': 'staged_candidate_uncompiled', 'lean_executed': False,
        'generator': pin(Path(__file__)), 'source': pin(args.output), 'tests': pin(args.tests),
        'input': pin(args.input or args.repository / RAW),
        'witness': pin(args.witness or args.repository / WITNESS),
        'dependency_pins': [pin(args.repository / rel) for rel in PINS if rel != RAW],
        'checks': checks, 'exact_actual_raw_source_reproduced': True,
        'audit_names': audit, 'audit_count': len(audit),
        'unique_graph_isomorphisms': len({b['isomorphism_theorem'] for b in bindings}),
        'occurrence_bindings': bindings,
        'scope': 'Only raw11 = 2 * raw02 and its linear assembly consequences; no geometric Mumford, Hodge, GW, product or CohFT acceptance'}
    args.ledger.write_text(json.dumps(ledger, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in ledger.items()
        if k not in ['occurrence_bindings', 'audit_names', 'dependency_pins']}, sort_keys=True))


if __name__ == '__main__':
    main()
