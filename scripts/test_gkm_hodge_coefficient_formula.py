#!/usr/bin/env python3
"""Pure controls for exact ordered formula replay; no Lean or Sage jobs."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
SCRIPT=ROOT/'scripts/export_gkm_hodge_coefficient_formula.py'
spec=importlib.util.spec_from_file_location('formula_exporter',SCRIPT)
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
full,c00,codec,emitter=f.dependencies()
packet=json.loads(f.INPUT.read_text(),object_pairs_hook=codec.unique_object)
SOURCE=ROOT/'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientFormula.lean'
TESTS=ROOT/'AxiomaticGWTest/GKM/HodgeDegreeZeroCoefficientFormula.lean'


def power(value,n):
    result=codec.RationalFunction.constant(1)
    for _ in range(n):result=result*value
    return result


def formula(w0,w1,a,b):
    return (-1)**(a+b)*power(w0,2-a)*power(w1,2-b)/(w0*w1)


def generator_degree(a):return [(0,0),(1,0),(0,1)][a]


class FormulaTests(unittest.TestCase):
    def test_exact_upstream_binding_and_generated_source(self):
        self.assertEqual(f.bind(packet,full,c00,codec,emitter),108)
        self.assertEqual(f.emit(c00,emitter),SOURCE.read_text())
        self.assertEqual(f.consumer_source(),TESTS.read_text())

    def test_all_108_ordered_field_identities_by_exact_cross_products(self):
        count=0
        for target in packet['targets']:
            for locus in target['fixed_loci']:
                w0,w1=map(codec.character,locus['tangent_characters'])
                self.assertNotEqual(w0*w1,0)
                for a in range(3):
                    for b in range(3):
                        actual=codec.RationalFunction.from_json(locus['hodge_pair_terms'][3*a+b]['coefficient'])
                        self.assertEqual(actual,formula(w0,w1,a,b))
                        count+=1
        self.assertEqual(count,108)

    def test_source_order_and_sign_are_not_interchangeable(self):
        locus=packet['targets'][0]['fixed_loci'][0]
        w0,w1=map(codec.character,locus['tangent_characters'])
        actual=codec.RationalFunction.from_json(locus['hodge_pair_terms'][1]['coefficient'])
        self.assertEqual(actual,formula(w0,w1,0,1))
        self.assertNotEqual(actual,formula(w1,w0,0,1))
        self.assertNotEqual(actual,(-1)*formula(w0,w1,0,1))

    def test_all_twelve_full_bivariate_polynomials(self):
        count=0
        for target in packet['targets']:
            for locus in target['fixed_loci']:
                w0,w1=map(codec.character,locus['tangent_characters'])
                incoming={};product={}
                left=[power(w0,2),(-1)*w0,codec.RationalFunction.constant(1)]
                right=[power(w1,2),(-1)*w1,codec.RationalFunction.constant(1)]
                for a in range(3):
                    for b in range(3):
                        i,j=generator_degree(a);k,l=generator_degree(b);key=(i+k,j+l)
                        actual=codec.RationalFunction.from_json(locus['hodge_pair_terms'][3*a+b]['coefficient'])
                        incoming[key]=incoming.get(key,0)+actual
                        product[key]=product.get(key,0)+left[a]*right[b]/(w0*w1)
                self.assertEqual(set(incoming),set(product))
                self.assertTrue(all(incoming[k]==product[k] for k in incoming))
                self.assertEqual(len(incoming),6)
                count+=1
        self.assertEqual(count,12)

    def test_every_coefficient_change_breaks_upstream_source_binding(self):
        count=0
        for ti,target in enumerate(packet['targets']):
            for pi,locus in enumerate(target['fixed_loci']):
                for i,_ in enumerate(locus['hodge_pair_terms']):
                    changed=deepcopy(packet)
                    q=changed['targets'][ti]['fixed_loci'][pi]['hodge_pair_terms'][i]['coefficient']['numerator'][0][1]
                    q[0]+=1000*q[1]
                    with self.assertRaises(ValueError):f.bind(changed,full,c00,codec,emitter)
                    count+=1
        self.assertEqual(count,108)

    def test_changed_order_and_formula_provenance_rejected(self):
        mutations=[lambda p:p['targets'][0]['fixed_loci'][0]['tangent_characters'].reverse(),
            lambda p:p['expanded_header']['gkm_packet_metadata'].__setitem__('formula','changed'),
            lambda p:p['expanded_header']['gkm_packet_metadata']['source']['python_sources'].__setitem__('gkm_localization/stable_map.py','0'*64)]
        for mutate in mutations:
            changed=deepcopy(packet);mutate(changed)
            with self.assertRaises(ValueError):f.bind(changed,full,c00,codec,emitter)

    def test_changed_helper_rejected_before_execution(self):
        with tempfile.TemporaryDirectory(prefix='formula-source-control-') as directory:
            root=Path(directory);sentinel=root/'executed';script=root/'scripts/export_gkm_hodge_coefficients.py'
            script.parent.mkdir();script.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            old=f.ROOT
            try:
                f.ROOT=root
                with self.assertRaises(ValueError):f.dependencies()
                self.assertFalse(sentinel.exists())
            finally:f.ROOT=old

    def test_no_heavy_import(self):
        self.assertFalse(any(n=='sage' or n.startswith('sage.') or n=='admcycles' or
            n.startswith('admcycles.') for n in sys.modules))

    def test_portable_CLI_and_no_overwrite(self):
        with tempfile.TemporaryDirectory(prefix='hodge-formula-cli-') as directory:
            root=Path(directory);output,tests,ledger=[root/n for n in ['out.lean','tests.lean','ledger.json']]
            command=[sys.executable,str(SCRIPT),'--output',str(output),'--tests',str(tests),'--ledger',str(ledger)]
            result=subprocess.run(command,cwd=root,capture_output=True,text=True,check=False)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(output.read_bytes(),SOURCE.read_bytes())
            self.assertEqual(tests.read_bytes(),TESTS.read_bytes())
            self.assertEqual(json.loads(ledger.read_text())['actual_coefficients'],108)
            self.assertFalse(json.loads(ledger.read_text())['lean_executed'])
            retry=subprocess.run(command,cwd=root,capture_output=True,text=True,check=False)
            self.assertNotEqual(retry.returncode,0)


if __name__=='__main__':unittest.main()
