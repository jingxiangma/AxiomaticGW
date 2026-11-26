#!/usr/bin/env python3
"""Decode all 108 compact-packet fractions and assemble all raw Hodge components.

The projection theorem is conditional on an existing homogeneous realization
and its fundamental-class normalization. It does not identify a Hodge/GW class
or prove a CohFT. Every positive-degree coefficient remains in the assembly.
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
C00_SHA = '40a111318d8fd8c42cfec82157690c60822df1fb23f12adb6062f7b6939d3cbe'
NAMESPACE = 'AxiomaticGW.GKM.HodgeDegreeZeroFullCoefficientReplay'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies():
    path = ROOT / 'scripts/export_gkm_hodge_c00.py'
    require(digest(path) == C00_SHA, 'Held c00 adapter changed before execution')
    spec = importlib.util.spec_from_file_location('held_hodge_c00', path)
    c00 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(c00)
    codec, emitter = c00.dependencies()
    return c00, codec, emitter


def validate(packet, c00, codec):
    c00.validate(packet, codec)
    count = 0
    for target in packet['targets']:
        for locus in target['fixed_loci']:
            for index, pair in enumerate(locus['hodge_pair_terms']):
                a, b = divmod(index, 3)
                require(pair['hodge_indices'] == [a, b] and
                        all(type(x) is int for x in pair['hodge_indices']),
                        'All nine ordered pairs must occur in held order')
                require(type(pair['source_pair_index']) is int and pair['source_pair_index'] == index,
                        'Wrong source pair reference')
                require(pair['components'] == [{'codimension': d, 'component_reference': {
                    'raw_component_index': d, 'raw_pair_index': index}} for d in range(5)],
                    'A component reference or explicit zero component changed')
                require(pair['hodge_codimension'] == a+b and
                        pair['equivariant_coefficient_codimension'] == 2-a-b and
                        pair['total_equivariant_codimension'] == 2,
                        'Recorded coefficient/stratum bidegrees changed')
                codec.RationalFunction.from_json(pair['coefficient'])
                count += 1
    require(count == 108, 'All 108 serialized fractions must occur')
    return count


def emit(packet, c00, shared):
    lines = ['/-', 'Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA', '-/', 'module', '',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientReplay',
        'public import AxiomaticGW.GKM.AdmcyclesHodgeStrataNormalization', '',
        '/-!', '# Complete exact coefficient assembly for the fixed compact candidate', '',
        f'Input SHA256: {INPUT_SHA}',
        'All 108 numerator/denominator pairs are actual incoming data, indexed by',
        'fixed point and both ordered lambda labels; all 540 component references remain.',
        'The realized sum contains every coefficient and all five raw degree components.',
        'Only its scalar projection is identified with the existing TFT correlator.',
        'No geometric Hodge/GRR identity, GW class, CohFT law or ordinary grading is assumed.',
        '-/', '', '@[expose] public section', '', f'namespace {NAMESPACE}', '',
        'open EquivariantCoefficients Matrix',
        'open AdmcyclesHodgeStrataNormalization', '',
        'noncomputable section', '', 'variable {C : StableCurveCohomology Coefficient}', '',
        'attribute [local instance] strataRealizationModule', '']
    vector = shared.vector
    for target, (_, _, name, _, size, _) in zip(packet['targets'], c00.FRAMES):
        lines.extend([f'namespace {name}', ''])
        for part in ['numerator','denominator']:
            loci=[]
            for locus in target['fixed_loci']:
                pairs=[shared.polynomial_text(pair['coefficient'][part],ring=True)
                       for pair in locus['hodge_pair_terms']]
                loci.append(vector([vector(pairs[3*a:3*a+3]) for a in range(3)]))
            lines.extend(['/-- Every actual incoming sparse polynomial, indexed by its full ordered key. -/',
                f'def {part}s : Fin {size} → Fin 3 → Fin 3 → Polynomial :=',
                '  '+vector(loci), ''])
        lines.extend([
            '/-- Every serialized fraction interpreted in the existing exact coefficient field. -/',
            f'def coefficients (p : Fin {size}) (a b : Fin 3) : Coefficient :=',
            '  embed (numerators p a b) / embed (denominators p a b)', '',
            '/-- Evaluation certifies denominator nonvanishing only, never a symbolic identity. -/',
            f'theorem denominator_ne_zero (p : Fin {size}) (a b : Fin 3) :',
            '    embed (denominators p a b) ≠ 0 := by',
            '  apply embed_ne_zero_of_eval _ ![2,3]',
            '  fin_cases p <;> fin_cases a <;> fin_cases b',
            '  all_goals norm_num only ['+c00.simp_text(['denominators','map_zero','map_one',
                'map_add','map_mul','map_pow','one_ne_zero','MvPolynomial.eval₂Hom_C',
                "MvPolynomial.eval₂Hom_X'",'RingHom.id_apply']+shared.VECTOR_SIMP)+']',
            '',
            '/-- The full tensor retains exactly the already checked incoming c00 entries. -/',
            f'theorem coefficients_zero_zero (p : Fin {size}) :',
            f'    coefficients p 0 0 = HodgeDegreeZeroCoefficientReplay.{name}.coefficient00 p := by',
            '  fin_cases p <;> rfl', '',
            '/-- The held c00 proof supplies the exact Euler units, with no new hypothesis. -/',
            f'theorem coefficients_zero_zero_eq_eulerUnits (p : Fin {size}) :',
            '    coefficients p 0 0 =',
            f'      (SurfaceReplay.{name}.accepted.eulerUnits p : Coefficient) :=',
            '  (coefficients_zero_zero p).trans',
            f'    (HodgeDegreeZeroCoefficientReplay.{name}.coefficient00_eq_eulerUnits p)', '',
            '/-- All actual coefficients and all actual raw components occur in this conditional class. -/',
            'noncomputable def candidateClass (A : StrataRealization C 2 (Fin 1)) :',
            '    C.H 2 (Fin 1) := assembly A coefficients', '',
            '/-- Projection of the complete candidate matches the existing fixed-point TFT. -/',
            'theorem scalar_candidateClass_eq_tft (D : ConnectedDegreeZero C)',
            '    (A : StrataRealization C 2 (Fin 1))',
            '    (hfund : A.map (StrataModule.basis',
            '      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :',
            '    D.scalar 2 (Fin 1) stable (candidateClass A) =',
            f'      (FixedPointAlgebra.algebra SurfaceReplay.{name}.accepted.eulerUnits).correlator',
            '        2 (Fin 1) (fun _ ↦ 1) :=',
            '  scalar_assembly_eq_tft D A hfund coefficients',
            f'    SurfaceReplay.{name}.accepted.eulerUnits coefficients_zero_zero_eq_eulerUnits', '',
            f'end {name}', ''])
    lines.extend(['end','',f'end {NAMESPACE}',''])
    return '\n'.join(lines)


def consumer_source():
    lines=['module','',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroFullCoefficientReplay','',
        '@[expose] public section','',
        'namespace AxiomaticGWTest.HodgeDegreeZeroFullCoefficientReplay','',
        'open AxiomaticGW AxiomaticGW.GKM','open EquivariantCoefficients',
        'open AdmcyclesHodgeStrataNormalization','',
        'variable {C : StableCurveCohomology Coefficient}','',
        'attribute [local instance] strataRealizationModule','']
    for name,size in [('Plane',3),('OneBlowup',4),('TwoBlowups',5)]:
        short=name[0].lower()+name[1:]
        lines.extend(['/-- Every positive and zero-degree coefficient has a checked denominator. -/',
            f'theorem {short}_all_denominators (p : Fin {size}) (a b : Fin 3) :',
            f'    embed (HodgeDegreeZeroFullCoefficientReplay.{name}.denominators p a b) ≠ 0 :=',
            f'  HodgeDegreeZeroFullCoefficientReplay.{name}.denominator_ne_zero p a b','',
            '/-- All coefficients occur before scalar projection, under the original realization inputs. -/',
            f'theorem {short}_complete_normalization (D : ConnectedDegreeZero C)',
            '    (A : StrataRealization C 2 (Fin 1))',
            '    (hfund : A.map (StrataModule.basis',
            '      (TautologicalStratum.fundamental 2 (Fin 1) stable)) = 1) :',
            f'    D.scalar 2 (Fin 1) stable (HodgeDegreeZeroFullCoefficientReplay.{name}.candidateClass A) =',
            f'      (FixedPointAlgebra.algebra SurfaceReplay.{name}.accepted.eulerUnits).correlator',
            '        2 (Fin 1) (fun _ ↦ 1) :=',
            f'  HodgeDegreeZeroFullCoefficientReplay.{name}.scalar_candidateClass_eq_tft D A hfund',''])
    lines.extend(['end AxiomaticGWTest.HodgeDegreeZeroFullCoefficientReplay',''])
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=INPUT)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--tests',type=Path,required=True)
    parser.add_argument('--ledger',type=Path,required=True)
    args=parser.parse_args()
    require(digest(args.input)==INPUT_SHA,'Fixed compact packet pin changed')
    outputs=[args.output,args.tests,args.ledger]
    require(len({p.resolve() for p in outputs})==3 and all(not p.exists() for p in outputs),
            'Outputs must be distinct new files')
    c00,codec,emitter=dependencies()
    packet=json.loads(args.input.read_text(),object_pairs_hook=codec.unique_object)
    count=validate(packet,c00,codec)
    source=emit(packet,c00,emitter)
    with args.output.open('x') as output:output.write(source)
    with args.tests.open('x') as output:output.write(consumer_source())
    record={'status':'generated_uncompiled','lean_executed':False,'sage_executed':False,
        'input':{'path':str(args.input),'sha256':digest(args.input)},
        'producer':{'path':str(Path(__file__)),'sha256':digest(Path(__file__))},
        'c00_helper_sha256':C00_SHA,'fractions':count,'component_references':540,
        'source':{'path':str(args.output),'sha256':digest(args.output)},
        'tests':{'path':str(args.tests),'sha256':digest(args.tests)},
        'scope':'Complete coefficient decoding and conditional scalar normalization; no geometric '
            'Hodge/Chern/GW/CohFT identification or equality of classes from scalar projection.'}
    with args.ledger.open('x') as output:output.write(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps(record,sort_keys=True))


if __name__=='__main__':main()
