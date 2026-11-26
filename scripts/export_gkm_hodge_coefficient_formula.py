#!/usr/bin/env python3
"""Bind every held coefficient to the ordered genus-two formal Chern formula.

The produced identities are exact field and formal-polynomial arithmetic.
They do not identify a Hodge bundle, realize a class, or establish a CohFT.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
PINS={'scripts/export_gkm_hodge_coefficients.py': '3d0e3180042e7324855f6cfa553a4cc55e071bf144198bf02802de856de56fee', 'scripts/export_gkm_hodge_c00.py': '0ee2f4d7aa4e44a4b81434e289bd18850e987ae5f63d3f87a35819b563308870', 'scripts/export_gkm_certificate.py': '54c5052adbb569fb7ed4172ac1600b04a5b31506f8a77c16dface1bbfe10f19c', 'scripts/check_gkm_inputs.py': 'ba2728773135a47a114b325287a098ece7165e95c6e7b5f8638f06e55c00376e', 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientReplay.lean': '68042b66b0ca52b452732dc42cd659de36618dae93adba1768162c78ace7d0d5', 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroFullCoefficientReplay.lean': '648ac71eb16d06ca1b94b29ca2e1972ca2f360ce534fb864230933daa6c29ce8', 'environments/gkm-degree-zero-hodge-strata-factored-candidate.json': '5be60671ddc68304610987123f048a6c010504cf27f3b690cd1e4d4e39227399'}
INPUT=ROOT/'environments/gkm-degree-zero-hodge-strata-factored-candidate.json'
NAMESPACE='AxiomaticGW.GKM.HodgeDegreeZeroCoefficientFormula'
HELD_FORMULA='sum_p product_j sum_{k=0,1,2} (-1)^k lambda_k w_{p,j}^{1-k}'
HELD_PRODUCER_SHA='4e88e18487577642f86bcf1d8762c8ac117d4bfe4329c095bbb6fdd38258c53a'


def require(ok,message):
    if not ok:raise ValueError(message)


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies():
    # Check every named input/helper first; execute only the held pure exporter.
    for relative,expected in PINS.items():
        require(digest(ROOT/relative)==expected,'Held source changed before helper execution: '+relative)
    path=ROOT/'scripts/export_gkm_hodge_coefficients.py'
    spec=importlib.util.spec_from_file_location('held_full_coefficient_exporter',path)
    full=importlib.util.module_from_spec(spec);spec.loader.exec_module(full)
    c00,codec,emitter=full.dependencies()
    return full,c00,codec,emitter


def bind(packet,full,c00,codec,emitter):
    full.validate(packet,c00,codec)
    metadata=packet['expanded_header']['gkm_packet_metadata']
    require(metadata['formula']==HELD_FORMULA and metadata['source']['python_sources'][
        'gkm_localization/stable_map.py']==HELD_PRODUCER_SHA,'Held ordered formula provenance changed')
    require(full.emit(packet,c00,emitter)==(ROOT/
        'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroFullCoefficientReplay.lean').read_text(),
        'Actual full coefficient data differ from the compiled upstream source')
    require(c00.emit(packet,emitter)==(ROOT/
        'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientReplay.lean').read_text(),
        'Actual ordered tangent data differ from the compiled upstream source')
    return 108


def emit(c00,shared):
    lines=['/-','Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA','-/','module','',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroFullCoefficientReplay',
        'public import Mathlib.Tactic.FinCases','public import Mathlib.Tactic.NormNum',
        'public import Mathlib.Tactic.Ring','',
        '/-!','# All actual ordered coefficients satisfy the formal genus-two Chern formula','',
        'The held producer orders lambda indices with its two ordered tangent weights.',
        'At genus two its coefficient is (-1)^(a+b) w₀^(1-a) w₁^(1-b).',
        'The equivalent common-denominator form below uses only natural exponents.',
        'Every equality is proved for the actual upstream decoded fraction, not a replacement.',
        'The bivariate variables are formal lambda₁ and lambda₂, with lambda₀ = 1.',
        'No geometric Hodge/Chern/GRR, GW, realization or CohFT identification is made.',
        '-/','', '@[expose] public section','',f'namespace {NAMESPACE}','',
        'open EquivariantCoefficients CurveConventionCertificate Matrix',
        'open scoped BigOperators','', 'noncomputable section','',
        '/-- Ordered rank-two Chern coefficient divided by the two tangent weights. -/',
        'def orderedChernCoefficient (w₀ w₁ : Coefficient) (a b : Fin 3) : Coefficient :=',
        '  (-1 : Coefficient) ^ (a.val + b.val) * w₀ ^ (2 - a.val) * w₁ ^ (2 - b.val) /',
        '    (w₀ * w₁)','',
        '/-- Two formal Hodge symbols over the existing exact equivariant field. -/',
        'abbrev HodgePolynomial := MvPolynomial (Fin 2) Coefficient','',
        '/-- Formal lambda₀, lambda₁ and lambda₂, with lambda₀ equal to one. -/',
        'def hodgeGenerator : Fin 3 → HodgePolynomial := ![1, MvPolynomial.X 0, MvPolynomial.X 1]','',
        '/-- Keep all nine ordered coefficients before collecting formal monomials. -/',
        'def hodgePolynomial (coeff : Fin 3 → Fin 3 → Coefficient) : HodgePolynomial :=',
        '  ∑ a, ∑ b, MvPolynomial.C (coeff a b) * hodgeGenerator a * hodgeGenerator b','',
        '/-- The rank-two formal Chern polynomial at one tangent weight. -/',
        'def chernPolynomial (w : Coefficient) : HodgePolynomial :=',
        '  MvPolynomial.C (w ^ 2) - MvPolynomial.C w * MvPolynomial.X 0 + MvPolynomial.X 1','',
        '/-- Algebraic expansion with shared formal Hodge symbols; no geometric class input. -/',
        'theorem hodgePolynomial_orderedChernCoefficient (w₀ w₁ : Coefficient) :',
        '    hodgePolynomial (orderedChernCoefficient w₀ w₁) =',
        '      MvPolynomial.C ((w₀ * w₁)⁻¹) * chernPolynomial w₀ * chernPolynomial w₁ := by',
        '  norm_num only ['+c00.simp_text(['hodgePolynomial','orderedChernCoefficient',
            'hodgeGenerator','chernPolynomial','Fin.sum_univ_succ','Fin.sum_univ_zero','div_eq_mul_inv',
            'map_mul','map_pow','map_neg','map_one']+shared.VECTOR_SIMP)+']',
        '  ring','']
    for _,_,name,_,size,_ in c00.FRAMES:
        full=f'HodgeDegreeZeroFullCoefficientReplay.{name}'
        low=f'HodgeDegreeZeroCoefficientReplay.{name}'
        lines.extend([f'namespace {name}','',
            '/-- Reuse the actual ordered tangent characters; no tangent table is substituted. -/',
            f'def tangentWeight (p : Fin {size}) (j : Fin 2) : Coefficient :=',
            f'  character ({low}.tangent p j)','',
            '/-- The actual product is nonzero because its already checked Euler weight is a unit. -/',
            f'theorem tangentProduct_ne_zero (p : Fin {size}) :',
            '    tangentWeight p 0 * tangentWeight p 1 ≠ 0 := by',
            f'  change character ({low}.tangent p 0) *',
            f'    character ({low}.tangent p 1) ≠ 0',
            f'  rw [← {low}.coefficient00_eq_tangentProduct,',
            f'    {low}.coefficient00_eq_eulerUnits]',
            f'  exact Units.ne_zero (SurfaceReplay.{name}.accepted.eulerUnits p)','',
            '/-- Every actual serialized coefficient agrees with the ordered source formula. -/',
            f'theorem coefficients_eq_orderedChern (p : Fin {size}) (a b : Fin 3) :',
            f'    {full}.coefficients p a b =',
            '      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) a b := by',
            f'  unfold {full}.coefficients orderedChernCoefficient',
            f'  apply (div_eq_div_iff ({full}.denominator_ne_zero p a b)',
            '    (tangentProduct_ne_zero p)).mpr',
            '  fin_cases p <;> fin_cases a <;> fin_cases b',
            '  all_goals norm_num only ['+c00.simp_text([f'{full}.numerators',
                f'{full}.denominators','tangentWeight',f'{low}.tangent','character']+
                shared.MAP_SIMP+shared.VECTOR_SIMP)+']',
            '  all_goals ring','',
            '/-- The complete actual bivariate polynomial factors into both formal Chern factors. -/',
            f'theorem hodgePolynomial_eq (p : Fin {size}) :',
            f'    hodgePolynomial ({full}.coefficients p) =',
            '      MvPolynomial.C ((tangentWeight p 0 * tangentWeight p 1)⁻¹) *',
            '        chernPolynomial (tangentWeight p 0) * chernPolynomial (tangentWeight p 1) := by',
            f'  have h : {full}.coefficients p =',
            '      orderedChernCoefficient (tangentWeight p 0) (tangentWeight p 1) := by',
            '    funext a b', '    exact coefficients_eq_orderedChern p a b',
            '  rw [h]', '  exact hodgePolynomial_orderedChernCoefficient _ _','',
            f'end {name}',''])
    lines.extend(['end','',f'end {NAMESPACE}',''])
    return '\n'.join(lines)


def consumer_source():
    lines=['module','',
        'public import AxiomaticGW.GKM.Fixtures.HodgeDegreeZeroCoefficientFormula','',
        '@[expose] public section','',
        'namespace AxiomaticGWTest.HodgeDegreeZeroCoefficientFormula','',
        'open AxiomaticGW.GKM HodgeDegreeZeroCoefficientFormula','']
    for name,size in [('Plane',3),('OneBlowup',4),('TwoBlowups',5)]:
        short=name[0].lower()+name[1:]
        lines.extend(['/-- Each source-ordered coefficient is checked, including the asymmetric pairs. -/',
            f'theorem {short}_all_coefficients (p : Fin {size}) (a b : Fin 3) :',
            f'    HodgeDegreeZeroFullCoefficientReplay.{name}.coefficients p a b =',
            f'      orderedChernCoefficient ({name}.tangentWeight p 0) ({name}.tangentWeight p 1) a b :=',
            f'  {name}.coefficients_eq_orderedChern p a b','',
            '/-- Formal polynomial equality is about the complete actual incoming coefficient tensor. -/',
            f'theorem {short}_full_polynomial (p : Fin {size}) :',
            f'    hodgePolynomial (HodgeDegreeZeroFullCoefficientReplay.{name}.coefficients p) =',
            f'      MvPolynomial.C (({name}.tangentWeight p 0 * {name}.tangentWeight p 1)⁻¹) *',
            f'        chernPolynomial ({name}.tangentWeight p 0) *',
            f'          chernPolynomial ({name}.tangentWeight p 1) :=',
            f'  {name}.hodgePolynomial_eq p',''])
    lines.extend(['end AxiomaticGWTest.HodgeDegreeZeroCoefficientFormula',''])
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=INPUT)
    for name in ['output','tests','ledger']:parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    require(digest(args.input)==PINS['environments/gkm-degree-zero-hodge-strata-factored-candidate.json'],
            'Fixed packet pin changed')
    outputs=[args.output,args.tests,args.ledger]
    require(len({p.resolve() for p in outputs})==3 and all(not p.exists() for p in outputs),
            'Output paths must be distinct new files')
    full,c00,codec,emitter=dependencies()
    packet=json.loads(args.input.read_text(),object_pairs_hook=codec.unique_object)
    count=bind(packet,full,c00,codec,emitter)
    for path,text in [(args.output,emit(c00,emitter)),(args.tests,consumer_source())]:
        with path.open('x') as out:out.write(text)
    record={'status':'generated_uncompiled','lean_executed':False,'sage_executed':False,
        'input':{'path':str(args.input),'sha256':digest(args.input)},'upstream_pins':PINS,
        'producer':{'path':str(Path(__file__)),'sha256':digest(Path(__file__))},
        'source':{'path':str(args.output),'sha256':digest(args.output)},
        'tests':{'path':str(args.tests),'sha256':digest(args.tests)},
        'actual_coefficients':count,'ordered_convention':'a ↦ tangent[0], b ↦ tangent[1]',
        'formula':'(-1)^(a+b) w0^(2-a) w1^(2-b) / (w0*w1)',
        'formal_polynomial':'(w0*w1)^(-1) (w0^2-lambda1*w0+lambda2) (w1^2-lambda1*w1+lambda2)',
        'boundary':'Exact arithmetic and formal polynomial identity only; no Hodge/GRR/GW/CohFT geometry.'}
    with args.ledger.open('x') as out:out.write(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps(record,sort_keys=True))


if __name__=='__main__':main()
