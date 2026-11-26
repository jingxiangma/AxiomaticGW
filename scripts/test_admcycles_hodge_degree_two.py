#!/usr/bin/env python3
"""Offline corruption controls and byte-identical replay of the fixed raw relation."""
import argparse
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(add_help=False)
parser.add_argument('--repository', type=Path, default=PACKAGE)
args, unittest_args = parser.parse_known_args()
sys.argv = [sys.argv[0]] + unittest_args
ROOT = args.repository
SCRIPT = PACKAGE / 'scripts/export_admcycles_hodge_degree_two.py'
spec = importlib.util.spec_from_file_location('hodge_degree_two_replay', SCRIPT)
f = importlib.util.module_from_spec(spec); spec.loader.exec_module(f)
wpath = PACKAGE / f.WITNESS
w = json.loads(wpath.read_text()); raw = json.loads((ROOT / f.RAW).read_text())
PROD = PACKAGE / 'AxiomaticGW/GKM/Fixtures/HodgeDegreeTwoRawRelation.lean'
TEST = PACKAGE / 'AxiomaticGWTest/GKM/HodgeDegreeTwoRawRelation.lean'

class Tests(unittest.TestCase):
    def test_complete_fixed_raw_occurrences(self):
        checks = f.validate(raw, w)
        self.assertEqual(checks['left_occurrences'], 28)
        self.assertEqual(checks['right_occurrences'], 16)
        self.assertEqual(checks['representatives'], 16)
        self.assertEqual(checks['exact_difference'], 0)

    def test_missing_duplicate_or_reordered_occurrence_rejected(self):
        for mode in ['omit', 'duplicate', 'reverse']:
            p = deepcopy(w)
            if mode == 'omit': p['mappings'].pop()
            elif mode == 'duplicate': p['mappings'][-1] = p['mappings'][0]
            else: p['mappings'].reverse()
            with self.assertRaises(ValueError): f.validate(raw, p)

    def test_requested_identity_and_normalization_are_fixed(self):
        for key, value in [('right_multiplier', [1, 1]), ('pair_indices', [2, 4]),
                           ('normalization', 'divide_by_automorphisms')]:
            p = deepcopy(w); p[key] = value
            with self.assertRaises(ValueError): f.validate(raw, p)

    def test_coefficients_and_source_flags_bound(self):
        for key in ['coefficient', 'admcycles_flag_map']:
            p = deepcopy(w); p['mappings'][0][key][0] = 999
            with self.assertRaises(ValueError): f.validate(raw, p)
        p = deepcopy(w); p['representatives'][0]['right_coefficient'] = [999, 1]
        with self.assertRaises(ValueError): f.validate(raw, p)

    def test_nonbijective_hint_and_sensitive_branch_rejected(self):
        p = deepcopy(w)
        r = next(r for r in p['mappings'] if len(r['hint']['vertices']) > 1)
        r['hint']['vertices'][1] = r['hint']['vertices'][0]
        with self.assertRaises(ValueError): f.validate(raw, p)
        p = deepcopy(w)
        for r in p['mappings']:
            G = f.term(raw, r['source'])['graph']
            edge = next((e for e in range(len(G['endpoints'])) if
                G['endpoints'][e][0] != G['endpoints'][e][1] or
                G['half_psi'][e][0] != G['half_psi'][e][1]), None)
            if edge is not None:
                r['hint']['swaps'][edge] = not r['hint']['swaps'][edge]
                break
        else: self.fail('Missing branch-sensitive source graph')
        with self.assertRaises(ValueError): f.validate(raw, p)

    def test_all_kappa_and_external_psi_are_preserved(self):
        r = w['mappings'][0]
        G = f.term(raw, r['source'])['graph']
        H = f.term(raw, w['representatives'][r['representative_index']]['source_reference'])['graph']
        for key in ['kappa', 'leg_psi']:
            bad = deepcopy(H)
            if key == 'kappa': bad[key][0][3] += 1
            else: bad[key][0] += 1
            with self.assertRaises(ValueError): f.hint_valid(G, bad, r['hint'])

    def test_exact_actual_source_and_consumer_replay(self):
        source, tests, bindings, audit, checks = f.prepare(ROOT, wpath)
        self.assertEqual(source, PROD.read_text()); self.assertEqual(tests, TEST.read_text())
        self.assertEqual(len(bindings), 44); self.assertEqual(len(set(audit)), 46)
        self.assertEqual(len({r['isomorphism_theorem'] for r in bindings}), 31)
        self.assertFalse(any(n == 'sage' or n.startswith('sage.') or n == 'admcycles' or
            n.startswith('admcycles.') for n in sys.modules))

    def test_independent_raw_and_witness_pins_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            bad = Path(d) / 'changed.json'
            bad.write_bytes((ROOT / f.RAW).read_bytes() + b'\n')
            with self.assertRaises(ValueError): f.prepare(ROOT, wpath, bad)
            bad.write_bytes(wpath.read_bytes() + b'\n')
            with self.assertRaises(ValueError): f.prepare(ROOT, bad)

    def test_changed_helper_is_not_executed(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d); helper = p / 'bad.py'; sentinel = p / 'executed'
            helper.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            with self.assertRaises(ValueError): f.load(helper, '0' * 64, 'must_not_execute')
            self.assertFalse(sentinel.exists())

    def test_cli_external_working_directory_and_no_overwrite(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d); prod, test, ledger = [p / n for n in ['p.lean', 't.lean', 'ledger.json']]
            cmd = [sys.executable, str(SCRIPT), '--repository', str(ROOT), '--witness', str(wpath),
                '--output', str(prod), '--tests', str(test), '--ledger', str(ledger)]
            done = subprocess.run(cmd, cwd=p, text=True, capture_output=True)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual(prod.read_bytes(), PROD.read_bytes())
            self.assertEqual(test.read_bytes(), TEST.read_bytes())
            self.assertFalse(json.loads(ledger.read_text())['lean_executed'])
            before = [x.read_bytes() for x in [prod, test, ledger]]
            done = subprocess.run(cmd, cwd=p, text=True, capture_output=True)
            self.assertNotEqual(done.returncode, 0)
            self.assertEqual(before, [x.read_bytes() for x in [prod, test, ledger]])

    def test_alias_outputs_fail_before_write(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d); out = p / 'same'; ledger = p / 'ledger'
            done = subprocess.run([sys.executable, str(SCRIPT), '--repository', str(ROOT),
                '--witness', str(wpath), '--output', str(out), '--tests', str(out),
                '--ledger', str(ledger)], text=True, capture_output=True)
            self.assertNotEqual(done.returncode, 0)
            self.assertFalse(out.exists()); self.assertFalse(ledger.exists())

if __name__ == '__main__': unittest.main()
