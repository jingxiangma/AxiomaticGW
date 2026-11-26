#!/usr/bin/env python3
"""Exact complete-sum controls; no geometric interpretation or heavy jobs."""
from copy import deepcopy
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
SCRIPT=ROOT/'scripts/export_gkm_hodge_regularity.py'
spec=importlib.util.spec_from_file_location('regularity_exporter',SCRIPT)
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
formula,full,c00,codec,emitter=f.dependencies()
packet=json.loads(f.INPUT.read_text(),object_pairs_hook=codec.unique_object)
SOURCE=ROOT/'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroRegularity.lean'
TESTS=ROOT/'AxiomaticGWTest/GKM/HodgeDegreeZeroRegularity.lean'


def collect(target):
    out={};gen=[(0,0),(1,0),(0,1)]
    for locus in target['fixed_loci']:
        for pair in locus['hodge_pair_terms']:
            a,b=pair['hodge_indices'];key=tuple(x+y for x,y in zip(gen[a],gen[b]))
            out[key]=out.get(key,codec.RationalFunction.constant(0))+codec.RationalFunction.from_json(pair['coefficient'])
    return out


def expected(sign,n,k):
    Q={(2,0):Fraction(sign),(1,1):Fraction(-sign),(0,2):Fraction(sign)}
    return {(0,0):codec.RationalFunction(Q),(1,0):codec.RationalFunction.constant(0),
            (0,1):codec.RationalFunction.constant(k),(2,0):codec.RationalFunction.constant(n),
            (1,1):codec.RationalFunction.constant(0),(0,2):codec.RationalFunction.constant(0)}


class RegularityTests(unittest.TestCase):
    def test_exact_binding_and_byte_replay(self):
        self.assertEqual(f.bind(packet,formula,full,c00,codec,emitter),108)
        self.assertEqual(f.emit(c00,emitter),SOURCE.read_text())
        self.assertEqual(f.consumer_source(),TESTS.read_text())

    def test_all_complete_actual_coefficients_equal_regular_lifts(self):
        for target,(sgn,n,k) in zip(packet['targets'],[(1,3,3),(0,4,0),(-1,5,-3)]):
            actual=collect(target);want=expected(sgn,n,k)
            self.assertEqual(set(actual),set(want))
            for key in want:self.assertEqual(actual[key],want[key])

    def test_zero_characters_apply_only_to_polynomial_lifts(self):
        for sign,n,k in [(1,3,3),(0,4,0),(-1,5,-3)]:
            lift=expected(sign,n,k)
            ordinary={key:value.ordinary() for key,value in lift.items()}
            self.assertEqual({key:value for key,value in ordinary.items() if value},
                {key:value for key,value in {(2,0):Fraction(n),(0,1):Fraction(k)}.items() if value})
        self.assertNotIn('Coefficient →+* ℚ',SOURCE.read_text())

    def test_omitting_a_fixed_locus_destroys_the_complete_identity(self):
        for target in packet['targets']:
            changed=deepcopy(target);changed['fixed_loci'].pop()
            # In particular the reciprocal-Euler coefficient no longer cancels.
            self.assertNotEqual(collect(changed)[(0,2)],0)

    def test_each_actual_coefficient_change_is_rejected(self):
        count=0
        for ti,target in enumerate(packet['targets']):
            for li,locus in enumerate(target['fixed_loci']):
                for pi,_ in enumerate(locus['hodge_pair_terms']):
                    changed=deepcopy(packet)
                    q=changed['targets'][ti]['fixed_loci'][li]['hodge_pair_terms'][pi]['coefficient']['numerator'][0][1]
                    q[0]+=1000*q[1]
                    with self.assertRaises(ValueError):f.bind(changed,formula,full,c00,codec,emitter)
                    count+=1
        self.assertEqual(count,108)

    def test_stale_source_fails_before_execution(self):
        with tempfile.TemporaryDirectory(prefix='regularity-pin-') as directory:
            root=Path(directory);sentinel=root/'executed'
            first=next(iter(f.PINS));path=root/first;path.parent.mkdir(parents=True)
            path.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            old=f.ROOT
            try:
                f.ROOT=root
                with self.assertRaises(ValueError):f.dependencies()
                self.assertFalse(sentinel.exists())
            finally:f.ROOT=old

    def test_no_heavy_imports(self):
        self.assertFalse(any(n=='sage' or n.startswith('sage.') or n=='admcycles' or n.startswith('admcycles.') for n in sys.modules))

    def test_portable_cli_and_no_overwrite(self):
        with tempfile.TemporaryDirectory(prefix='regularity-cli-') as directory:
            root=Path(directory);out,test,ledger=[root/n for n in ['out.lean','test.lean','ledger.json']]
            cmd=[sys.executable,str(SCRIPT),'--output',str(out),'--tests',str(test),'--ledger',str(ledger)]
            result=subprocess.run(cmd,cwd=root,capture_output=True,text=True,check=False)
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(out.read_bytes(),SOURCE.read_bytes());self.assertEqual(test.read_bytes(),TESTS.read_bytes())
            self.assertEqual(json.loads(ledger.read_text())['actual_coefficients'],108)
            self.assertNotEqual(subprocess.run(cmd,cwd=root,capture_output=True,check=False).returncode,0)


if __name__=='__main__':unittest.main()
