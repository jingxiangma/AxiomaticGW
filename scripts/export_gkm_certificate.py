#!/usr/bin/env python3
"""Emit kernel proof replay for the exact classical GKM state-space tables.

The independent Python checker is a preflight, not a proof oracle. Every
emitted certificate proves acceptance against a fixed Lean surface request.
No CohFT classes, curve graph, or numerical GW value is certified here.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

import check_gkm_inputs as codec


ROOT = Path(__file__).resolve().parents[1]
FRAMES = [('X0', 'Plane', 3), ('X1', 'OneBlowup', 4), ('X2', 'TwoBlowups', 5)]


def rational_text(q):
    q = Fraction(q)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator}/{q.denominator})'


def polynomial_text(terms, ring=False):
    terms = codec.polynomial(terms)
    if not terms:
        return '0'
    result = []
    for (a, b), q in terms.items():
        coefficient = f'MvPolynomial.C ({rational_text(q)} : ℚ)' if ring else rational_text(q)
        factors = [f'({coefficient})'] if ring or q != 1 else []
        for exponent, variable in [(a, 'MvPolynomial.X 0' if ring else 'x'),
                                   (b, 'MvPolynomial.X 1' if ring else 'y')]:
            if exponent:
                factors.append(f'({variable})' if exponent == 1 else f'({variable})^{exponent}')
        result.append('*'.join(factors) if factors else '1')
    return (' + '.join(result) if len(' + '.join(result)) < 68 else '\n    + '.join(result))


def vector(items):
    text = '![' + ', '.join(items) + ']'
    return text if len(text) < 70 and '\n' not in text else '![\n    ' + ',\n    '.join(items) + ']' 


def matrix(items):
    return '!![\n    ' + ';\n    '.join(', '.join(row) for row in items) + ']' 


def key(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def nonvanishing_point(terms):
    """Find an exact evaluation witness; Lean checks its nonzero value."""
    polynomial = codec.polynomial(terms)
    codec.require(bool(polynomial), 'Cannot certify a zero polynomial')
    def nonzero(a, b):
        return sum(q * a**i * b**j for (i, j), q in polynomial.items()) != 0
    if nonzero(2, 3):
        return 2, 3
    for a in range(1, max(i for i, _ in polynomial) + 2):
        for b in range(1, max(j for _, j in polynomial) + 2):
            if nonzero(a, b):
                return a, b
    raise ValueError('No nonvanishing witness on the degree-bounded evaluation grid')


def has_variable_denominator(values):
    """Choose proof tactics from expression shape, never an acceptance result."""
    if isinstance(values, dict):
        return any(a or b for a, b in codec.polynomial(values['denominator']))
    return any(has_variable_denominator(value) for value in values)


def regular_variable_denominators(values):
    """Regular nonconstant factors may change form during denominator clearing."""
    if isinstance(values, dict):
        terms = codec.polynomial(values['denominator'])
        return [values['denominator']] if terms.get((0, 0)) and any(a or b for a, b in terms) else []
    return [terms for value in values for terms in regular_variable_denominators(value)]


VECTOR_SIMP = ['Matrix.cons_val', 'Matrix.of_apply', 'Matrix.cons_val_zero\'', 'Matrix.cons_val_succ\'',
               'Matrix.cons_val_zero', 'Matrix.cons_val_succ', 'Matrix.cons_val_fin_one',
               'Matrix.cons_val_one', 'Fin.mk.injEq', 'Fin.ext_iff', 'Fin.val_succ', 'Fin.val_zero',
               'Fin.val_natCast', 'Fin.val_one\'', 'ite_true', 'ite_false']
BASIC_SIMP = ['one_mul', 'mul_one', 'zero_mul', 'mul_zero', 'zero_add', 'add_zero',
              'div_one', 'pow_zero', 'pow_one', 'neg_one_mul', 'neg_zero', 'sub_zero',
              'zero_sub', 'sub_self']
MAP_SIMP = ['map_zero', 'map_one', 'map_add', 'map_mul', 'map_pow', 'embed_C', 'embed_X_zero', 'embed_X_one'] + BASIC_SIMP
EVAL_SIMP = ['atZero', 'map_zero', 'map_one', 'map_add', 'map_mul', 'map_pow', 'MvPolynomial.eval₂Hom_C',
             "MvPolynomial.eval₂Hom_X'", 'RingHom.id_apply', 'Pi.zero_apply']
MATRIX_SIMP = ['Matrix.mul_apply', 'Matrix.mulVec', 'dotProduct', 'Matrix.transpose_apply',
               'Matrix.col_apply', 'Matrix.diagonal', 'Matrix.one_apply', 'Pi.mul_apply',
               'Pi.one_apply', 'Fin.sum_univ_succ', 'Fintype.sum_empty']
ORDINARY_SIMP = ['SurfaceCohomology.tracePairing_counit_apply', 'SurfaceCohomology.cupProduct',
                 'SurfaceCohomology.divisorIntersection', 'SurfaceCohomology.hyperplane',
                 'SurfaceCohomology.exceptional', 'SurfaceCohomology.point',
                 'SurfaceCohomology.one_coordinates', 'SurfaceCohomology.firstChernDivisor_val',
                 'SurfaceCohomology.hyperplaneDivisor', 'SurfaceCohomology.exceptionalDivisor',
                 'Submodule.coe_sub', 'Submodule.coe_smul', 'Submodule.coe_sum',
                 'Prod.fst_zero', 'Prod.snd_zero', 'Prod.fst_add', 'Prod.snd_add',
                 'Prod.fst_sub', 'Prod.snd_sub', 'Prod.smul_fst', 'Prod.smul_snd',
                 'Pi.zero_apply', 'Pi.add_apply', 'Pi.sub_apply', 'Pi.smul_apply',
                 'Pi.single_apply', 'Finset.sum_apply', 'smul_eq_mul',
                 'Fin.sum_univ_succ', 'Fintype.sum_empty']


def simp_text(names):
    return ',\n      '.join(dict.fromkeys(names))


def emit(report, targets=None):
    codec.check_report(report)
    lines = ['/-', 'Copyright (c) 2026 JMA. All rights reserved.',
             'Released under Apache 2.0 license as described in the file LICENSE.',
             'Authors: JMA', '-/', 'module', '',
             'public import AxiomaticGW.GKM.Fixtures.SurfaceFrames',
             'public import Mathlib.Tactic.FinCases',
             'public import Mathlib.Tactic.FieldSimp', 'public import Mathlib.Tactic.NormNum',
             'public import Mathlib.Tactic.Ring', '',
             '/-!', '# Kernel replay of the fixed GKM classical state spaces', '',
             'Generated by scripts/export_gkm_certificate.py from exact candidate data.',
             'Every acceptance proof is bound to an independently held surface request.',
             'Ordinary comparisons specialize complete sums, not individual poles.',
             'This proves neither geometric applicability nor a numerical GW invariant.', '-/', '',
             '@[expose] public section', '', 'namespace AxiomaticGW.GKM.SurfaceReplay', '',
             'open EquivariantCoefficients StateSpaceCertificate', 'open Matrix', '',
             'noncomputable section', '',
             '/-- The character square is nonzero in the field normalizer\'s polynomial form. -/',
             'private theorem difference_square_ne_zero :',
             '    x*(-(y*2)+x) + y^2 ≠ 0 := by',
             '  rw [show x*(-(y*2)+x) + y^2 = (x-y)^2 by ring]',
             '  exact pow_ne_zero 2 x_sub_y_ne_zero', '',
             '/-- Reversing the character order gives the same nonzero square. -/',
             'private theorem reverse_difference_square_ne_zero :',
             '    y*(-(x*2)+y) + x^2 ≠ 0 := by',
             '  rw [show y*(-(x*2)+y) + x^2 = (y-x)^2 by ring]',
             '  exact pow_ne_zero 2 y_sub_x_ne_zero']
    for frame, (target, name, n) in zip(report['targets'], FRAMES):
        codec.require(frame['target'] == target, 'Changed fixed target order')
        if targets is not None and target not in targets:
            continue
        values = []
        lookup = {}
        def value(v):
            codec.RationalFunction.from_json(v)
            k = key(v)
            if k not in lookup:
                lookup[k] = len(values)
                values.append(v)
            return f'values {lookup[k]}'
        fields = {
            'restrictions': matrix([[value(v) for v in row] for row in frame['basis_to_fixedpoint']]),
            'inverse': matrix([[value(v) for v in row] for row in frame['fixedpoint_to_basis']]),
            'euler': vector([value(v) for v in frame['euler']]),
            'metric': matrix([[value(v) for v in row] for row in frame['metric']]),
            'inverseMetric': matrix([[value(v) for v in row] for row in frame['inverse_metric']]),
            'products': vector([vector([vector([value(v) for v in coefficients])
                                       for coefficients in row]) for row in frame['products']]),
            'c1': vector([value(v) for v in frame['c1_coordinates']])}
        polynomials = {}
        for v in values:
            polynomials[key(v['denominator'])] = v['denominator']
        for v in frame['euler']:
            polynomials[key(v['numerator'])] = v['numerator']
        lines += ['', f'namespace {name}', '', '/-- Exact sparse polynomial numerators. -/',
                  f'def numerators : Fin {len(values)} → Polynomial :=',
                  '  ' + vector([polynomial_text(v['numerator'], True) for v in values]), '',
                  '/-- Exact sparse polynomial denominators, including equivalent representatives. -/',
                  f'def denominators : Fin {len(values)} → Polynomial :=',
                  '  ' + vector([polynomial_text(v['denominator'], True) for v in values]), '',
                  '/-- Candidate values interpreted in the genuine fraction field. -/',
                  f'def values (i : Fin {len(values)}) : Coefficient :=',
                  '  embed (numerators i) / embed (denominators i)', '',
                  '/-- A regular candidate value has the stated representative specialization. -/',
                  f'theorem specializes_value (i : Fin {len(values)}) (v : ℚ)',
                  '    (hd : atZero (denominators i) ≠ 0)',
                  '    (hv : atZero (numerators i) / atZero (denominators i) = v) :',
                  '    Specializes (values i) v :=',
                  '  ⟨numerators i, denominators i, hd, rfl, hv⟩']
        for terms in [ [[[1,0],[1,1]]], [[[0,1],[1,1]]],
                       [[[0,1],[-1,1]],[[1,0],[1,1]]],
                       [[[0,1],[1,1]],[[1,0],[-1,1]]] ]:
            polynomials[key(terms)] = terms
        nonzero = []
        nonzero_by_polynomial = {}
        for index, terms in enumerate(polynomials.values()):
            lemma = f'denominator_{index}_ne_zero'
            nonzero.append(lemma)
            nonzero_by_polynomial[key(terms)] = lemma
            a, b = nonvanishing_point(terms)
            lines += ['', '/-- Exact nonvanishing, certified by polynomial evaluation only for this purpose. -/',
                      f'theorem {lemma} :',
                      f'    ({polynomial_text(terms)} : Coefficient) ≠ 0 := by',
                      '  have h := embed_ne_zero_of_eval',
                      f'    ({polynomial_text(terms, True)}) ![{a},{b}] (by',
                      '    norm_num only [' + simp_text(EVAL_SIMP[1:] + VECTOR_SIMP) + '])',
                      '  norm_num only [' + simp_text(MAP_SIMP) + '] at h ⊢', '  all_goals exact h']
        lines += ['', '/-- Candidate state-space tables from the exported JSON. -/',
                  f'def tables : Tables {n} where']
        lines += [f'  {field} := {expression}' for field, expression in fields.items()]
        algebra_simp = ['tables', 'values', 'numerators', 'denominators',
                        f'SurfaceFrames.{name}.request'] + VECTOR_SIMP + MAP_SIMP + MATRIX_SIMP
        polynomial_fields = {
            'restrictions_eq': frame['basis_to_fixedpoint'],
            'euler_eq': frame['euler'],
            'products_eq': [frame['basis_to_fixedpoint'], frame['products']],
            'unit_eq': frame['basis_to_fixedpoint'],
            'c1_eq': [frame['basis_to_fixedpoint'], frame['c1_coordinates']],
        }
        field_inputs = {
            **polynomial_fields,
            'restrictions_inverse': [frame['basis_to_fixedpoint'], frame['fixedpoint_to_basis']],
            'inverse_restrictions': [frame['basis_to_fixedpoint'], frame['fixedpoint_to_basis']],
            'metric_eq': [frame['basis_to_fixedpoint'], frame['euler'], frame['metric']],
            'inverseMetric_eq': [frame['fixedpoint_to_basis'], frame['euler'], frame['inverse_metric']],
        }
        lines += ['', 'set_option maxHeartbeats 4000000 in',
                  '-- Replay checks both inverse matrices and up to 125 product coefficients.',
                  '/-- All exact table identities and ordinary comparisons are kernel checked.',
                  'The larger local budget covers the finite matrix and product coefficient replay. -/',
                  f'theorem accepted : Accepts SurfaceFrames.{name}.request tables where']
        for field, cases in [('restrictions_eq', ['i', 'j']), ('euler_eq', ['i']),
                             ('euler_ne_zero', ['i']), ('restrictions_inverse', ['i', 'j']),
                             ('inverse_restrictions', ['i', 'j']), ('metric_eq', ['i', 'j']),
                             ('inverseMetric_eq', ['i', 'j']), ('products_eq', ['i', 'j', 'p']),
                             ('unit_eq', ['i']), ('c1_eq', ['i'])]:
            lines += [f'  {field} := by']
            if field == 'euler_ne_zero':
                lines += ['    intro i', '    fin_cases i']
                for v in frame['euler']:
                    hn = nonzero_by_polynomial[key(v['numerator'])]
                    hd = nonzero_by_polynomial[key(v['denominator'])]
                    lines += ['    · change embed (' + polynomial_text(v['numerator'], True) + ') /',
                              '        embed (' + polynomial_text(v['denominator'], True) + ') ≠ 0',
                              f'      have h := div_ne_zero {hn} {hd}',
                              '      norm_num only [' + simp_text(MAP_SIMP) + '] at h ⊢',
                              '      exact h']
                continue
            elif field == 'products_eq':
                lines += ['    intro i j', '    ext p']
            else:
                lines += ['    ext ' + ' '.join(cases)]
            lines += ['    ' + ' <;> '.join('fin_cases ' + c for c in cases) + ' <;>',
                      '      dsimp only [tables, values, numerators, denominators, Matrix.cons_val,',
                      '        Matrix.of_apply, SurfaceFrames.' + name + '.request]',
                      '    all_goals norm_num only [' + simp_text(algebra_simp) + ']']
            if field in polynomial_fields and not has_variable_denominator(polynomial_fields[field]):
                if field != 'unit_eq':
                    lines += ['    all_goals ring']
            else:
                lines += ['    all_goals try field_simp [' + simp_text(['x_ne_zero', 'y_ne_zero',
                          'x_sub_y_ne_zero', 'y_sub_x_ne_zero'] + nonzero) + ']',
                          '    all_goals ring_nf',
                          '    all_goals try field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero,',
                          '      y_sub_x_ne_zero, neg_x_add_y_ne_zero, neg_y_add_x_ne_zero,',
                          '      difference_square_ne_zero, reverse_difference_square_ne_zero]']
                regular_factors = dict.fromkeys(key(p) for p in regular_variable_denominators(field_inputs[field]))
                for factor in regular_factors:
                    lemma = nonzero_by_polynomial[factor]
                    lines += ['    all_goals try field_simp (disch :=',
                              f'      convert {lemma} using 1; ring)']
                lines += ['    all_goals ring']
        for field, cases in [('metric_specializes', ['i', 'j']),
                             ('products_specialize', ['i', 'j', 'k']),
                             ('c1_specializes', ['i'])]:
            lines += [f'  {field} := by', '    intro ' + ' '.join(cases),
                      '    ' + ' <;> '.join('fin_cases ' + c for c in cases) + ' <;>',
                      '      dsimp only [tables, Matrix.cons_val, Matrix.of_apply] <;>',
                      '      apply specializes_value <;>',
                      '      dsimp only [numerators, denominators, Matrix.cons_val,',
                      '        SurfaceFrames.' + name + '.request, SurfaceFrames.' + name + '.states,',
                      '        SurfaceFrames.' + name + '.coordinates] <;>',
                      '      norm_num only [' + simp_text(
                          ['numerators', 'denominators', f'SurfaceFrames.{name}.request',
                           f'SurfaceFrames.{name}.states', f'SurfaceFrames.{name}.coordinates']
                          + EVAL_SIMP + VECTOR_SIMP + ORDINARY_SIMP) + ']']
        lines += ['', f'end {name}']
    lines += ['', 'end', '', 'end AxiomaticGW.GKM.SurfaceReplay', '']
    if any('convert denominator_' in line for line in lines):
        lines.insert(lines.index('public import Mathlib.Tactic.FieldSimp'),
                     'public import Mathlib.Tactic.Convert')
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?', default=ROOT / 'environments/gkm-inputs-osx-arm64.json')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--target', action='append', choices=[frame[0] for frame in FRAMES],
                        help='Replay only the selected target(s); defaults to all three')
    args = parser.parse_args()
    report = json.loads(args.input.read_text(), object_pairs_hook=codec.unique_object)
    output = emit(report, args.target)
    args.output.write_text(output)
    print(json.dumps({'status': 'emitted_candidate_proof', 'output': str(args.output),
                      'targets': [t[0] for t in FRAMES if args.target is None or t[0] in args.target],
                      'scope': 'classical state-space tables; Lean compilation still required'}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(f'GKM certificate export FAILED: {error}', file=sys.stderr)
        raise SystemExit(1)
