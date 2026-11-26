#!/usr/bin/env python3
"""Replay complete fixed-point pole cancellation and regular formal specialization.

All actual ordered fractions are retained upstream. The lift lives over QQ[x,y],
so zero-character evaluation is never applied to the full localized field.
No geometric Hodge product, GW class, or CohFT is identified here.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
PINS={'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientReplay.lean': '0b2ab996b5e331bef42e1465a4b6c99307a605393f12077d1c950824f0ea48c6', 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroFullCoefficientReplay.lean': '648ac71eb16d06ca1b94b29ca2e1972ca2f360ce534fb864230933daa6c29ce8', 'environments/gkm-degree-zero-hodge-strata-factored-candidate.json': '5be60671ddc68304610987123f048a6c010504cf27f3b690cd1e4d4e39227399', 'scripts/check_gkm_inputs.py': 'ba2728773135a47a114b325287a098ece7165e95c6e7b5f8638f06e55c00376e', 'scripts/export_gkm_certificate.py': '54c5052adbb569fb7ed4172ac1600b04a5b31506f8a77c16dface1bbfe10f19c', 'scripts/export_gkm_hodge_c00.py': '40a111318d8fd8c42cfec82157690c60822df1fb23f12adb6062f7b6939d3cbe', 'scripts/export_gkm_hodge_coefficients.py': '0caee1d95f14791ed90b28b5b9b9a0e9a2501aab63192fdfb5f76231a87a6c47', 'scripts/export_gkm_hodge_coefficient_formula.py': '53d121bd07b6b266775f96ca01e558d9a220617ecf93d807598de6e7dc0f4e6f', 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientFormula.lean': '516d3d3a07e7411fb2f76f427829d329dd96ae9c4b1ea89b6ea150fdb11fc35c', 'AxiomaticGWTest/GKM/HodgeDegreeZeroCoefficientFormula.lean': '563e9f19677d15ec45616c89d15ee5c5e02fdf6db0178464fb78a55b62fa10aa'}
INPUT=ROOT/'environments/gkm-degree-zero-hodge-strata-factored-candidate.json'
NAMESPACE='AxiomaticGW.GKM.HodgeDegreeZeroRegularity'


def require(ok,message):
    if not ok:raise ValueError(message)


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies():
    for rel,expected in PINS.items():
        require(digest(ROOT/rel)==expected,'Held source changed before execution: '+rel)
    path=ROOT/'scripts/export_gkm_hodge_coefficient_formula.py'
    spec=importlib.util.spec_from_file_location('held_formula_exporter',path)
    f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
    full,c00,codec,emitter=f.dependencies()
    return f,full,c00,codec,emitter


def bind(packet,f,full,c00,codec,emitter):
    require(f.bind(packet,full,c00,codec,emitter)==108,'Incomplete actual coefficient frame')
    require(f.emit(c00,emitter)==(ROOT/'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientFormula.lean').read_text(),
            'Ordered formula source differs from upstream')
    require(f.consumer_source()==(ROOT/'AxiomaticGWTest/GKM/HodgeDegreeZeroCoefficientFormula.lean').read_text(),
            'Ordered formula consumer differs from upstream')
    return 108


def emit(c00,shared):
    simp=c00.simp_text
    lines=['/-','Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA','-/','module','',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientFormula',
        'public import Mathlib.Tactic.FieldSimp','',
        '/-!','# Complete fixed-point pole cancellation for formal Hodge polynomials','',
        'Each complete sum uses all actual incoming ordered coefficients.',
        'Its explicit lift has polynomial torus-character coefficients, and only that',
        'lift is evaluated at zero. The lambda symbols remain formal indeterminates.',
        'No field-to-QQ evaluation, geometric Hodge product, Mumford relation, GW class',
        'identification, localization theorem or CohFT law is asserted.','-/','',
        '@[expose] public section','','set_option autoImplicit false','',f'namespace {NAMESPACE}','',
        'open EquivariantCoefficients HodgeDegreeZeroCoefficientFormula',
        'open CurveConventionCertificate Matrix','open scoped BigOperators','',
        'noncomputable section','',
        '/-- Polynomial torus-character coefficients with two separate formal Hodge variables. -/',
        'abbrev RegularHodgePolynomial := MvPolynomial (Fin 2) Polynomial','',
        '/-- Rational formal Hodge polynomials after setting only torus characters to zero. -/',
        'abbrev OrdinaryHodgePolynomial := MvPolynomial (Fin 2) ℚ','',
        '/-- The six monomials collect all nine ordered entries, retaining asymmetric sums. -/',
        'theorem hodgePolynomial_expansion (c : Fin 3 → Fin 3 → Coefficient) :',
        '    hodgePolynomial c =',
        '      MvPolynomial.C (c 0 0) + MvPolynomial.C (c 0 1 + c 1 0) * MvPolynomial.X 0 +',
        '      MvPolynomial.C (c 0 2 + c 2 0) * MvPolynomial.X 1 +',
        '      MvPolynomial.C (c 1 1) * MvPolynomial.X 0 ^ 2 +',
        '      MvPolynomial.C (c 1 2 + c 2 1) * MvPolynomial.X 0 * MvPolynomial.X 1 +',
        '      MvPolynomial.C (c 2 2) * MvPolynomial.X 1 ^ 2 := by',
        '  norm_num only ['+simp(['hodgePolynomial','hodgeGenerator','Fin.sum_univ_three',
             'map_add','Matrix.cons_val_zero','Matrix.cons_val_one','Matrix.cons_val_two',
             'Matrix.head_cons','Matrix.tail_cons'])+']',
        '  ring','']
    for name,size,k,sgn in [('Plane',3,3,1),('OneBlowup',4,0,0),('TwoBlowups',5,-3,-1)]:
        full=f'HodgeDegreeZeroFullCoefficientReplay.{name}'
        form=f'HodgeDegreeZeroCoefficientFormula.{name}'
        low=f'HodgeDegreeZeroCoefficientReplay.{name}'
        q='MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2'
        ep=q if sgn==1 else ('-('+q+')' if sgn==-1 else '0')
        fieldq='x ^ 2 - x * y + y ^ 2'
        ev=fieldq if sgn==1 else ('-('+fieldq+')' if sgn==-1 else '0')
        lines.extend([f'namespace {name}','',
            '/-- Complete fixed-point sum of the actual decoded coefficient polynomials. -/',
            'def completePolynomial : HodgePolynomial :=',
            f'  ∑ p : Fin {size}, hodgePolynomial ({full}.coefficients p)','',
            '/-- Explicit polynomial lift; the inner variables are the two torus characters. -/',
            'def regularLift : RegularHodgePolynomial :=',
            '  MvPolynomial.C ('+ep.replace(' - ', ' -\n    ').replace(' + ', ' +\n    ')+') +',
            f'    {size} * MvPolynomial.X 0 ^ 2 + ({k}) * MvPolynomial.X 1','',
            '/-- The ordinary formal polynomial, retaining both independent Hodge symbols. -/',
            'def ordinaryPolynomial : OrdinaryHodgePolynomial :=',
            f'  {size} * MvPolynomial.X 0 ^ 2 + ({k}) * MvPolynomial.X 1',''])
        expressions=[('constant',f'{full}.coefficients p 0 0',ev),
            ('lambda1',f'{full}.coefficients p 0 1 + {full}.coefficients p 1 0','0'),
            ('lambda2',f'{full}.coefficients p 0 2 + {full}.coefficients p 2 0',str(k)),
            ('lambda1Squared',f'{full}.coefficients p 1 1',str(size)),
            ('mixed',f'{full}.coefficients p 1 2 + {full}.coefficients p 2 1','0'),
            ('lambda2Squared',f'{full}.coefficients p 2 2','0')]
        for label,expression,value in expressions:
            lines.extend(['/-- Exact cancellation in the complete fixed-point coefficient sum. -/',
                f'theorem sum_{label} :',f'    (∑ p : Fin {size},',
                '      ('+expression.replace(' + ', ' +\n       ')+')) =',f'      {value} := by',
                '  norm_num only ['+simp([form+'.coefficients_eq_orderedChern',
                    'orderedChernCoefficient',form+'.tangentWeight',low+'.tangent','character',
                    'Fin.sum_univ_succ','Fin.sum_univ_zero','Fin.val_two']+
                    shared.MAP_SIMP+shared.VECTOR_SIMP)+']',
                '  ring_nf',
                '  field_simp [x_ne_zero, y_ne_zero, x_sub_y_ne_zero, y_sub_x_ne_zero,',
                '    neg_x_add_y_ne_zero, neg_y_add_x_ne_zero]', '  ring',''])
        lines.extend(['/-- The full localized expression is the image of one polynomial lift. -/',
            'theorem map_embed_regularLift :',
            '    MvPolynomial.map embed regularLift = completePolynomial := by',
            '  simp only [completePolynomial, hodgePolynomial_expansion, Finset.sum_add_distrib,',
            '    ← Finset.sum_mul, ← map_sum]',
            '  simp only [← Finset.sum_add_distrib]',
            '  rw [sum_constant, sum_lambda1, sum_lambda2, sum_lambda1Squared, sum_mixed,',
            '    sum_lambda2Squared]',
            '  norm_num only [regularLift, map_add, map_sub, map_neg, map_mul, map_pow,',
            '    map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,',
            '    embed_X_zero, embed_X_one, map_zero, zero_mul, zero_add, add_zero]',
            *(['  ring'] if k != 0 else []), '',
            '/-- Evaluate the polynomial lift at zero only after all fixed-point poles cancel. -/',
            'theorem map_atZero_regularLift :',
            '    MvPolynomial.map atZero regularLift = ordinaryPolynomial := by',
            '  norm_num only [regularLift, ordinaryPolynomial, atZero, map_add, map_sub, map_neg,',
            '    map_mul, map_pow, map_natCast, map_ofNat, map_intCast, MvPolynomial.map_C, MvPolynomial.map_X,',
            "    MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero, zero_mul, mul_zero, zero_add,", 
            '    add_zero, zero_pow, sub_zero, neg_zero]','',
            f'end {name}',''])
    lines.extend(['end','',f'end {NAMESPACE}',''])
    return '\n'.join(lines)


def consumer_source():
    lines=['module','','public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroRegularity','',
        '@[expose] public section','','namespace AxiomaticGWTest.HodgeDegreeZeroRegularity','',
        'open AxiomaticGW.GKM HodgeDegreeZeroRegularity','']
    for name,n,k in [('Plane',3,3),('OneBlowup',4,0),('TwoBlowups',5,-3)]:
        short=name[0].lower()+name[1:]
        lines.extend(['/-- An explicit regular lift witnesses the complete actual fixed-point sum. -/',
            f'theorem {short}_regular_specialization :',
            '    ∃ P : RegularHodgePolynomial,',
            f'      MvPolynomial.map EquivariantCoefficients.embed P = {name}.completePolynomial ∧',
            f'      MvPolynomial.map EquivariantCoefficients.atZero P =',
            f'        {n} * MvPolynomial.X 0 ^ 2 + ({k}) * MvPolynomial.X 1 :=',
            f'  ⟨{name}.regularLift, {name}.map_embed_regularLift, {name}.map_atZero_regularLift⟩',''])
    lines.extend(['end AxiomaticGWTest.HodgeDegreeZeroRegularity',''])
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=INPUT)
    for n in ['output','tests','ledger']:parser.add_argument('--'+n,type=Path,required=True)
    args=parser.parse_args()
    require(digest(args.input)==PINS['environments/gkm-degree-zero-hodge-strata-factored-candidate.json'],
            'Fixed complete packet changed')
    outputs=[args.output,args.tests,args.ledger]
    require(len({p.resolve() for p in outputs})==3 and all(not p.exists() for p in outputs),
            'Outputs must be distinct new files')
    f,full,c00,codec,emitter=dependencies()
    packet=json.loads(args.input.read_text(),object_pairs_hook=codec.unique_object)
    count=bind(packet,f,full,c00,codec,emitter)
    for path,text in [(args.output,emit(c00,emitter)),(args.tests,consumer_source())]:
        with path.open('x') as out:out.write(text)
    record={'status':'generated_uncompiled','upstream_pins':PINS,'actual_coefficients':count,
        'producer':{'path':str(Path(__file__)),'sha256':digest(Path(__file__))},
        'source':{'path':str(args.output),'sha256':digest(args.output)},
        'tests':{'path':str(args.tests),'sha256':digest(args.tests)},
        'input':{'path':str(args.input),'sha256':digest(args.input)},
        'lean_executed':False,'sage_executed':False,
        'scope':'Complete actual formal polynomial sum, explicit polynomial lift and its zero-character image; no geometric Hodge/GW/CohFT identity.'}
    with args.ledger.open('x') as out:out.write(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps(record,sort_keys=True))


if __name__=='__main__':main()
