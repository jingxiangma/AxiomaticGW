#!/usr/bin/env python3
"""Offline preservation controls for all 108 coefficients and 540 components.

No proof assistant or Sage process is invoked. The scalar projection theorem
is not used as a test that the higher-degree class is correct.
"""

from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/export_gkm_hodge_coefficients.py'
spec = importlib.util.spec_from_file_location('full_hodge_exporter', SCRIPT)
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
c00, codec, emitter = f.dependencies()
packet = json.loads(f.INPUT.read_text(), object_pairs_hook=codec.unique_object)
SOURCE = ROOT / 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroFullCoefficientReplay.lean'
TESTS = ROOT / 'AxiomaticGWTest/GKM/HodgeDegreeZeroFullCoefficientReplay.lean'


class FullCoefficientTests(unittest.TestCase):
    def test_all_pairs_components_and_exact_source_replay(self):
        self.assertEqual(f.digest(f.INPUT), f.INPUT_SHA)
        self.assertEqual(f.validate(packet,c00,codec),108)
        self.assertEqual(f.emit(packet,c00,emitter),SOURCE.read_text())
        self.assertEqual(f.consumer_source(),TESTS.read_text())
        self.assertEqual(sum(len(pair['components']) for t in packet['targets']
            for l in t['fixed_loci'] for pair in l['hodge_pair_terms']),540)

    def test_each_of_the_108_coefficients_is_actually_consumed(self):
        held=SOURCE.read_text()
        checked=0
        for ti,target in enumerate(packet['targets']):
            for li,locus in enumerate(target['fixed_loci']):
                for pi,_ in enumerate(locus['hodge_pair_terms']):
                    changed=deepcopy(packet)
                    q=changed['targets'][ti]['fixed_loci'][li]['hodge_pair_terms'][pi][
                        'coefficient']['numerator'][0][1]
                    q[0] += 1000*q[1]
                    self.assertEqual(f.validate(changed,c00,codec),108)
                    self.assertNotEqual(f.emit(changed,c00,emitter),held,(ti,li,pi))
                    checked+=1
        self.assertEqual(checked,108)

    def test_every_denominator_is_nonzero_at_the_proposed_witness(self):
        for target in packet['targets']:
            for locus in target['fixed_loci']:
                for pair in locus['hodge_pair_terms']:
                    terms=codec.polynomial(pair['coefficient']['denominator'])
                    self.assertNotEqual(sum(q*2**a*3**b for (a,b),q in terms.items()),0)

    def test_actual_c00_retained_in_every_target(self):
        for target in packet['targets']:
            for locus in target['fixed_loci']:
                self.assertEqual(locus['hodge_pair_terms'][0]['coefficient'],locus['tangent_euler'])
        source=SOURCE.read_text()
        for name in ['Plane','OneBlowup','TwoBlowups']:
            self.assertIn(f'HodgeDegreeZeroCoefficientReplay.{name}.coefficient00 p',source)

    def test_positive_coefficient_change_preserved_before_projection(self):
        changed=deepcopy(packet)
        changed['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8]['coefficient']['numerator'][0][1][0]=7
        self.assertEqual(f.validate(changed,c00,codec),108)
        text=f.emit(changed,c00,emitter)
        self.assertNotEqual(text,SOURCE.read_text())
        self.assertIn('MvPolynomial.C (7 : ℚ)',text)
        self.assertIn('C.H 2 (Fin 1) := assembly A coefficients',text)
        self.assertNotIn('candidateClass A = 1',text)

    def test_ordered_pair_and_component_reference_mutations_rejected(self):
        mutations=[
            lambda p:p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8].__setitem__('hodge_indices',[1,2]),
            lambda p:p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8].__setitem__('source_pair_index',7),
            lambda p:p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8]['components'].pop(),
            lambda p:p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8]['components'][2]['component_reference'].__setitem__('raw_pair_index',7),
            lambda p:p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8].__setitem__('equivariant_coefficient_codimension',0),
            lambda p:p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][8]['coefficient'].__setitem__('denominator',[])]
        for mutate in mutations:
            changed=deepcopy(packet);mutate(changed)
            with self.assertRaises(ValueError):f.validate(changed,c00,codec)

    def test_no_heavy_runtime_import(self):
        self.assertFalse(any(n=='sage' or n.startswith('sage.') or n=='admcycles' or
            n.startswith('admcycles.') for n in sys.modules))

    def test_portable_CLI_replay(self):
        with tempfile.TemporaryDirectory(prefix='full-hodge-cli-') as directory:
            root=Path(directory)
            output,tests,ledger=[root/n for n in ['out.lean','tests.lean','ledger.json']]
            command=[sys.executable,str(SCRIPT),'--output',str(output),
                     '--tests',str(tests),'--ledger',str(ledger)]
            result=subprocess.run(command,cwd=root,capture_output=True,text=True,check=False)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(output.read_bytes(),SOURCE.read_bytes())
            self.assertEqual(tests.read_bytes(),TESTS.read_bytes())
            record=json.loads(ledger.read_text())
            self.assertEqual(record['fractions'],108)
            self.assertEqual(record['component_references'],540)
            self.assertFalse(record['lean_executed'])
            retry=subprocess.run(command,cwd=root,capture_output=True,text=True,check=False)
            self.assertNotEqual(retry.returncode,0)


if __name__=='__main__':unittest.main()
