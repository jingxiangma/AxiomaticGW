#!/usr/bin/env python3
"""Replay the fixed compact Hodge packet's twelve actual c00 coefficients.

Only this finite degree-zero coefficient sector is decoded. The genuine
QQ(x,y) field, fan frames, ordered producer tangents and accepted Euler units
are existing project definitions. No geometric Hodge or CohFT claim is made.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'environments/gkm-degree-zero-hodge-strata-factored-candidate.json'
INPUT_SHA = '5be60671ddc68304610987123f048a6c010504cf27f3b690cd1e4d4e39227399'
PINS = {
    'scripts/check_gkm_inputs.py': 'ba2728773135a47a114b325287a098ece7165e95c6e7b5f8638f06e55c00376e',
    'scripts/export_gkm_certificate.py': '54c5052adbb569fb7ed4172ac1600b04a5b31506f8a77c16dface1bbfe10f19c',
}
FRAMES = [('X0', 'P2', 'Plane', 'plane', 3, 1),
          ('X1', 'F1', 'OneBlowup', 'hirzebruchOne', 4, 2),
          ('X2', 'Bl2P2', 'TwoBlowups', 'blowupTwo', 5, 3)]
NAMESPACE = 'AxiomaticGW.GKM.HodgeDegreeZeroCoefficientReplay'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path, name, expected):
    require(digest(path) == expected, f'Helper source changed before execution: {path}')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def dependencies():
    # Verify both files first. The existing emitter imports its named codec;
    # bind that import to the checked module, then restore the caller's entry.
    for relative, expected in PINS.items():
        require(digest(ROOT / relative) == expected, f'Helper source changed: {relative}')
    codec = load(ROOT / 'scripts/check_gkm_inputs.py', 'held_gkm_codec',
                 PINS['scripts/check_gkm_inputs.py'])
    previous = sys.modules.get('check_gkm_inputs')
    sys.modules['check_gkm_inputs'] = codec
    try:
        emitter = load(ROOT / 'scripts/export_gkm_certificate.py', 'held_gkm_emitter',
                       PINS['scripts/export_gkm_certificate.py'])
    finally:
        if previous is None:
            del sys.modules['check_gkm_inputs']
        else:
            sys.modules['check_gkm_inputs'] = previous
    require(emitter.codec is codec, 'Polynomial emitter imported another codec')
    return codec, emitter


def finite(value, bound):
    require(type(value) is int and 0 <= value < bound, 'Invalid finite label')
    return value


def validate(packet, codec):
    """Validate the exact finite sector; identities remain Lean obligations."""
    require(packet['schema_version'] == 1 and packet['kind'] ==
        'gkm_localization.degree_zero_factored_raw_hodge_strata_candidate', 'Wrong packet kind')
    require(packet['proof_status'] == 'candidate_self_contained_factored_raw_strata' and
        all(v is False for v in packet['claims'].values()), 'Candidate scope changed')
    require(len(packet['targets']) == 3, 'Missing fixed target')
    total = 0
    for target, (key, research, _, _, size, curve_size) in zip(packet['targets'], FRAMES):
        require(target['target'] == key and target['research_target'] == research,
                'Fixed target order or identification changed')
        require(type(target['genus']) is int and target['genus'] == 2 and
                target['stable_curve_space'] == 'Mbar_2_1', 'Wrong genus/moduli frame')
        require(target['markings'] == [{'basis_index': 0, 'basis_name': 'unit',
                'label': 0, 'psi': 0}], 'Wrong fixed unit insertion')
        curve = target['full_curve_class']['coordinates']
        require(len(curve) == curve_size and all(type(x) is int and x == 0 for x in curve),
                'Wrong complete degree-zero class')
        require(len(target['fixed_loci']) == size, 'Missing fixed point')
        for ordinal, locus in enumerate(target['fixed_loci']):
            require(finite(locus['fixed_point_index'], size) == ordinal,
                    'Fixed-point indices reordered or duplicated')
            require(len(locus['fixed_point']) == 2, 'Wrong fixed-point cone')
            for ray in locus['fixed_point']:
                finite(ray, size)
            weights = locus['tangent_characters']
            require(len(weights) == 2 and all(len(w) == 2 for w in weights) and
                    all(type(c) is int for w in weights for c in w),
                    'Wrong exact ordered tangent characters')
            require(locus['stable_vertex'] == {'edges': [], 'full_curve_class': curve,
                    'genus': 2, 'marking_labels': [0]}, 'Stable vertex or class changed')
            require(type(locus['graph_automorphism_denominator']) is int and
                    locus['graph_automorphism_denominator'] == 1, 'Wrong one-vertex symmetry factor')
            codec.RationalFunction.from_json(locus['tangent_euler'])
            codec.RationalFunction.from_json(locus['unit_restriction'])
            require(len(locus['hodge_pair_terms']) == 9, 'Missing pair frame')
            pair = locus['hodge_pair_terms'][0]
            require(pair['hodge_indices'] == [0, 0] and pair['source_pair_index'] == 0 and
                    pair['hodge_codimension'] == 0 and pair['equivariant_coefficient_codimension'] == 2 and
                    pair['total_equivariant_codimension'] == 2 and pair['lambda_zero_is_one'] is True,
                    'Wrong fixed c00 pair metadata')
            require(pair['components'] == [{'codimension': d, 'component_reference': {
                'raw_component_index': d, 'raw_pair_index': 0}} for d in range(5)],
                'Wrong raw c00 component references')
            codec.RationalFunction.from_json(pair['coefficient'])
            total += 1
    require(total == 12, 'The finite sector must contain twelve fixed points')
    return total


def simp_text(names):
    """Keep the existing explicit simp set, with readable bounded-width lines."""
    rows, current = [], ''
    for name in dict.fromkeys(names):
        if current and len(current) + len(name) + 2 > 66:
            rows.append(current)
            current = name
        else:
            current += (', ' if current else '') + name
    if current:
        rows.append(current)
    return ',\n      '.join(rows)


def emit(packet, shared):
    lines = ['/-', 'Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA', '-/', 'module', '',
        'public import AxiomaticGW.GKM.Fixtures.CurveReplay',
        'public import AxiomaticGW.GKM.Fixtures.SurfaceReplay', '',
        '/-!', '# Actual c00 coefficients of the compact degree-zero candidate', '',
        f'Input SHA256: {INPUT_SHA}',
        'The digest records provenance; identities use the decoded field expressions.',
        'All twelve fixed-point indices, cones and both ordered tangent characters remain.',
        'This is symbolic arithmetic in the existing equivariant fraction field.',
        'No ordinary grading, Hodge identification, GW class or CohFT geometry is assumed.',
        '-/', '', '@[expose] public section', '', f'namespace {NAMESPACE}', '',
        'open EquivariantCoefficients CurveConventionCertificate Matrix', '',
        'noncomputable section', '']
    vector = shared.vector
    finite_text = lambda x: f'⟨{x}, by decide⟩'
    for target, (_, _, name, surface, size, curve_size) in zip(packet['targets'], FRAMES):
        loci = target['fixed_loci']
        lines.extend([f'namespace {name}', '',
            '/-- Actual complete degree-zero class from the incoming target record. -/',
            f'def fullCurveClass : SurfaceTarget.{surface}.Curve :=',
            '  ' + vector([str(x) for x in target['full_curve_class']['coordinates']]), '',
            '/-- All effective coordinates are retained and checked. -/',
            'theorem fullCurveClass_eq_zero : fullCurveClass = 0 := by decide +kernel', '',
            '/-- Incoming fixed-point identifiers, without modular integer coercion. -/',
            f'def fixedPointIndex : Fin {size} → Fin {size} :=',
            '  ' + vector([finite_text(l['fixed_point_index']) for l in loci]), '',
            '/-- Every fixed point occurs in the held order. -/',
            'theorem fixedPointIndex_eq : fixedPointIndex = id := by decide +kernel', '',
            '/-- Incoming cone labels in the fixed fan-ray frame. -/',
            f'def fixedPoints : Fin {size} → Fin 2 → Fin {size} :=',
            '  ' + vector([vector([finite_text(x) for x in l['fixed_point']]) for l in loci]), '',
            '/-- Cone labels bind the same fixed-point interpretation as the existing request. -/',
            f'theorem fixedPoints_eq : fixedPoints = CurveFrames.{name}.request.points := by',
            '  decide +kernel', '',
            '/-- Both ordered incoming integer tangent characters. -/',
            f'def tangent : Fin {size} → Fin 2 → Fin 2 → ℤ :=',
            '  ' + vector([vector([vector([str(c) for c in w]) for w in l['tangent_characters']])
                           for l in loci]), '',
            '/-- The actual branch order agrees with the already replayed producer table. -/',
            f'theorem tangent_eq_replay : tangent = CurveReplay.{name}.tables.tangent := by',
            '  decide +kernel', ''])
        for stem, select in [('c00', lambda l: l['hodge_pair_terms'][0]['coefficient']),
                             ('serializedEuler', lambda l: l['tangent_euler']),
                             ('unit', lambda l: l['unit_restriction'])]:
            for part in ['numerator', 'denominator']:
                lines.extend([
                    '/-- Exact incoming sparse polynomial, without changing its fraction representative. -/',
                    f'def {stem}_{part} : Fin {size} → Polynomial :=',
                    '  ' + vector([shared.polynomial_text(select(l)[part], ring=True) for l in loci]), ''])
            value_name = {'c00': 'coefficient00', 'serializedEuler': 'serializedTangentEuler',
                          'unit': 'unitRestriction'}[stem]
            lines.extend(['/-- The actual serialized numerator divided by its serialized denominator. -/',
                f'def {value_name} (p : Fin {size}) : Coefficient :=',
                f'  embed ({stem}_numerator p) / embed ({stem}_denominator p)', '',
                '/-- Every serialized denominator is checked nonzero in the genuine coefficient field. -/',
                f'theorem {stem}_denominator_ne_zero (p : Fin {size}) :',
                f'    embed ({stem}_denominator p) ≠ 0 := by',
                '  fin_cases p',
                '  all_goals norm_num only [' + simp_text([f'{stem}_denominator'] +
                    shared.MAP_SIMP + shared.VECTOR_SIMP) + ']',
                '  all_goals exact one_ne_zero', ''])
        lines.extend([
            '/-- The actual c00 coefficient and serialized tangent Euler field agree. -/',
            f'theorem coefficient00_eq_serializedEuler (p : Fin {size}) :',
            '    coefficient00 p = serializedTangentEuler p := by',
            '  rfl', '',
            '/-- Exact symbolic multiplication of both incoming tangent characters. -/',
            f'theorem coefficient00_eq_tangentProduct (p : Fin {size}) :',
            '    coefficient00 p = character (tangent p 0) * character (tangent p 1) := by',
            '  fin_cases p',
            '  all_goals norm_num only [' + simp_text([
                'coefficient00','c00_numerator','c00_denominator','tangent','character'] +
                shared.MAP_SIMP + shared.VECTOR_SIMP) + ']',
            '  all_goals ring', '',
            '/-- The incoming unit restriction is exactly one at every fixed point. -/',
            f'theorem unitRestriction_eq_one (p : Fin {size}) : unitRestriction p = 1 := by',
            '  fin_cases p',
            '  all_goals norm_num only [' + simp_text([
                'unitRestriction','unit_numerator','unit_denominator'] + shared.MAP_SIMP +
                shared.VECTOR_SIMP) + ']', '',
            '/-- The checked producer tangent pair gives the independently held Euler factor. -/',
            f'theorem coefficient00_eq_requestEuler (p : Fin {size}) :',
            f'    coefficient00 p = SurfaceFrames.{name}.request.euler p := by',
            '  rw [coefficient00_eq_tangentProduct, tangent_eq_replay]',
            f'  rcases CurveReplay.{name}.accepted.tangent_eq p with ⟨h0, h1⟩ | ⟨h0, h1⟩',
            '  · rw [h0, h1]',
            f'    exact (CurveReplay.{name}.accepted.state_euler p).symm',
            '  · rw [h0, h1, mul_comm]',
            f'    exact (CurveReplay.{name}.accepted.state_euler p).symm', '',
            '/-- This is the exact invertible Euler weight used by the existing fixed-point algebra. -/',
            f'theorem coefficient00_eq_eulerUnits (p : Fin {size}) :',
            f'    coefficient00 p = (SurfaceReplay.{name}.accepted.eulerUnits p : Coefficient) := by',
            f'  change coefficient00 p = SurfaceReplay.{name}.tables.euler p',
            f'  rw [SurfaceReplay.{name}.accepted.euler_eq]',
            '  exact coefficient00_eq_requestEuler p', '',
            f'end {name}', ''])
    lines.extend(['end', '', f'end {NAMESPACE}', ''])
    return '\n'.join(lines)


def consumer_source():
    lines = ['module', '',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientReplay', '',
        '@[expose] public section', '',
        'namespace AxiomaticGWTest.HodgeDegreeZeroCoefficientReplay', '',
        'open AxiomaticGW.GKM', 'open EquivariantCoefficients', '']
    for _, _, name, _, size, _ in FRAMES:
        lines.extend([
            '/-- Every actual incoming c00 entry supplies the normalization consumer. -/',
            f'theorem {name[0].lower()+name[1:]}_all_c00 (p : Fin {size}) :',
            f'    HodgeDegreeZeroCoefficientReplay.{name}.coefficient00 p =',
            f'      (SurfaceReplay.{name}.accepted.eulerUnits p : Coefficient) :=',
            f'  HodgeDegreeZeroCoefficientReplay.{name}.coefficient00_eq_eulerUnits p', ''])
    lines.extend(['end AxiomaticGWTest.HodgeDegreeZeroCoefficientReplay', ''])
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=INPUT)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tests', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    args = parser.parse_args()
    require(digest(args.input) == INPUT_SHA, 'Fixed compact packet pin changed')
    require(len({p.resolve() for p in [args.output,args.tests,args.ledger]}) == 3 and
            all(not p.exists() for p in [args.output,args.tests,args.ledger]),
            'Outputs must be distinct new files')
    codec, emitter = dependencies()
    packet = json.loads(args.input.read_text(), object_pairs_hook=codec.unique_object)
    count = validate(packet, codec)
    source = emit(packet, emitter)
    with args.output.open('x') as output:
        output.write(source)
    with args.tests.open('x') as output:
        output.write(consumer_source())
    record = {'status':'generated_uncompiled', 'lean_executed':False, 'sage_executed':False,
        'input':{'path':str(args.input),'sha256':digest(args.input)},
        'producer':{'path':str(Path(__file__)),'sha256':digest(Path(__file__))},
        'helpers':PINS, 'fixed_point_coefficients':count,
        'source':{'path':str(args.output),'sha256':digest(args.output)},
        'tests':{'path':str(args.tests),'sha256':digest(args.tests)},
        'scope':'Only actual c00 fractions, full degree-zero classes, fixed-point identity, '
            'both tangent characters and Euler-unit normalization; no other Hodge pairs or geometry.'}
    with args.ledger.open('x') as output:
        output.write(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps(record,sort_keys=True))


if __name__ == '__main__':
    main()
