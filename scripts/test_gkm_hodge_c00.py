#!/usr/bin/env python3
"""Pure source-binding controls for the fixed twelve-entry c00 replay.

No Lean/Sage runs. A changed but well-formed coefficient is deliberately
emitted into changed kernel obligations; Python does not certify identities.
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
SCRIPT = ROOT / 'scripts/export_gkm_hodge_c00.py'
spec = importlib.util.spec_from_file_location('c00_exporter', SCRIPT)
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
codec, emitter = f.dependencies()
packet = json.loads(f.INPUT.read_text(), object_pairs_hook=codec.unique_object)
SOURCE = ROOT / 'AxiomaticGW/GKM/Fixtures/HodgeDegreeZeroCoefficientReplay.lean'
TESTS = ROOT / 'AxiomaticGWTest/GKM/HodgeDegreeZeroCoefficientReplay.lean'


class C00Tests(unittest.TestCase):
    def test_complete_packet_and_source_replay(self):
        self.assertEqual(f.digest(f.INPUT), f.INPUT_SHA)
        self.assertEqual(f.validate(packet, codec), 12)
        self.assertEqual(f.emit(packet, emitter), SOURCE.read_text())
        self.assertEqual(f.consumer_source(), TESTS.read_text())
        self.assertEqual([len(t['fixed_loci']) for t in packet['targets']], [3, 4, 5])

    def test_existing_exact_field_arithmetic_confirms_all_twelve(self):
        # Supplemental exact arithmetic only. Lean checks the emitted identities.
        for target in packet['targets']:
            for locus in target['fixed_loci']:
                coefficient = codec.RationalFunction.from_json(locus['hodge_pair_terms'][0]['coefficient'])
                euler = codec.RationalFunction.from_json(locus['tangent_euler'])
                weights = [codec.RationalFunction({(1, 0): codec.Fraction(w[0]),
                    (0, 1): codec.Fraction(w[1])}) for w in locus['tangent_characters']]
                self.assertEqual(coefficient, euler)
                self.assertEqual(coefficient, weights[0] * weights[1])

    def test_every_incoming_fraction_occurs_in_output(self):
        text = f.emit(packet, emitter)
        for target in packet['targets']:
            for locus in target['fixed_loci']:
                for value in [locus['hodge_pair_terms'][0]['coefficient'],
                              locus['tangent_euler'], locus['unit_restriction']]:
                    for part in ['numerator', 'denominator']:
                        self.assertIn(emitter.polynomial_text(value[part], ring=True), text)

    def test_changed_well_formed_coefficient_changes_actual_Lean_data(self):
        changed = deepcopy(packet)
        for target in changed['targets']:
            for locus in target['fixed_loci']:
                locus['hodge_pair_terms'][0]['coefficient']['numerator'][0][1][0] *= 2
        self.assertEqual(f.validate(changed, codec), 12)
        text = f.emit(changed, emitter)
        self.assertNotEqual(text, SOURCE.read_text())
        self.assertIn('MvPolynomial.C (2 : ℚ)', text)
        for name in ['Plane', 'OneBlowup', 'TwoBlowups']:
            self.assertIn(f'coefficient00 p = SurfaceFrames.{name}.request.euler p', text)

    def test_changed_cone_or_tangent_is_not_silently_replaced(self):
        for field in ['fixed_point', 'tangent_characters']:
            changed = deepcopy(packet)
            locus = changed['targets'][0]['fixed_loci'][0]
            if field == 'fixed_point':
                locus[field] = [0, 2]
            else:
                locus[field][0][0] = 2
            self.assertEqual(f.validate(changed, codec), 12)
            self.assertNotEqual(f.emit(changed, emitter), SOURCE.read_text())

    def test_malformed_or_misbound_metadata_rejected(self):
        mutations = [lambda p: p['targets'].pop(),
            lambda p: p['targets'][0]['fixed_loci'].pop(),
            lambda p: p['targets'][0]['fixed_loci'][0].__setitem__('fixed_point_index', 3),
            lambda p: p['targets'][0]['fixed_loci'][0].__setitem__('fixed_point_index', True),
            lambda p: p['targets'][0]['fixed_loci'][0].__setitem__('fixed_point', [0, 3]),
            lambda p: p['targets'][0]['fixed_loci'][0].__setitem__('tangent_characters', [[1, 0]]),
            lambda p: p['targets'][0]['full_curve_class']['coordinates'].__setitem__(0, 1),
            lambda p: p['targets'][0]['markings'][0].__setitem__('psi', 1),
            lambda p: p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][0].__setitem__('hodge_indices', [0, 1]),
            lambda p: p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][0]['components'].pop(),
            lambda p: p['targets'][0]['fixed_loci'][0]['hodge_pair_terms'][0]['coefficient'].__setitem__('denominator', [])]
        for mutate in mutations:
            changed = deepcopy(packet)
            mutate(changed)
            with self.assertRaises(ValueError):
                f.validate(changed, codec)

    def test_stale_helper_rejected_before_execution(self):
        with tempfile.TemporaryDirectory(prefix='c00-source-pin-') as directory:
            root = Path(directory)
            sentinel = root / 'executed'
            helper = root / 'helper.py'
            helper.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            with self.assertRaises(ValueError):
                f.load(helper, 'bad_helper', '0' * 64)
            self.assertFalse(sentinel.exists())

    def test_duplicate_JSON_key_rejected(self):
        with self.assertRaises(ValueError):
            json.loads('{"a":1,"a":2}', object_pairs_hook=codec.unique_object)

    def test_no_Sage_or_admcycles_import(self):
        self.assertFalse(any(n == 'sage' or n.startswith('sage.') or n == 'admcycles' or
                             n.startswith('admcycles.') for n in sys.modules))

    def test_portable_CLI_replay_and_no_overwrite(self):
        with tempfile.TemporaryDirectory(prefix='c00-cli-') as directory:
            root = Path(directory)
            out, tests, ledger = [root / n for n in ['out.lean', 'tests.lean', 'ledger.json']]
            command = [sys.executable, str(SCRIPT), '--output', str(out),
                       '--tests', str(tests), '--ledger', str(ledger)]
            result = subprocess.run(command, cwd=root, capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(out.read_bytes(), SOURCE.read_bytes())
            self.assertEqual(tests.read_bytes(), TESTS.read_bytes())
            self.assertFalse(json.loads(ledger.read_text())['lean_executed'])
            before = [p.read_bytes() for p in [out, tests, ledger]]
            retry = subprocess.run(command, cwd=root, capture_output=True, text=True, check=False)
            self.assertNotEqual(retry.returncode, 0)
            self.assertEqual(before, [p.read_bytes() for p in [out, tests, ledger]])


if __name__ == '__main__':
    unittest.main()
