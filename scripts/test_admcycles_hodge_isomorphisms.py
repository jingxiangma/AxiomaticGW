#!/usr/bin/env python3
"""Offline exact grouping, witness rejection and byte-identical Lean replay.

No Sage, Lean, graph search or relation search is executed. The fixed witness
and actual raw packet remain independently pinned and all occurrences retained.
"""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/export_admcycles_hodge_isomorphisms.py'
spec = importlib.util.spec_from_file_location('isomorphism_certificate', SCRIPT)
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)
w = json.loads(f.WITNESS.read_text())
PRODUCTION = ROOT / 'AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataIsomorphisms.lean'
CONSUMER = ROOT / 'AxiomaticGWTest/GKM/AdmcyclesHodgeStrataIsomorphisms.lean'

class Tests(unittest.TestCase):
    def test_complete_occurrences_and_exact_QQ_grouping(self):
        r = f.validate(w)
        self.assertEqual(r['raw_occurrences_checked'], 230)
        self.assertEqual(r['representatives'], 44)
        self.assertEqual(r['nonzero_grouped_coordinates'], 44)
        self.assertEqual(r['exact_grouped_difference'], 0)
        self.assertEqual(sum(x['source']['pair_index'] == 5 for x in w['mappings']), 122)
        self.assertEqual(sum(x['source']['pair_index'] == 7 for x in w['mappings']), 108)

    def test_omitted_occurrence_rejected(self):
        p = deepcopy(w);p['mappings'].pop()
        with self.assertRaises(ValueError): f.validate(p)

    def test_duplicate_occurrence_rejected(self):
        p = deepcopy(w);p['mappings'][-1] = p['mappings'][0]
        with self.assertRaises(ValueError): f.validate(p)

    def test_nonbijective_vertex_hint_rejected(self):
        p = deepcopy(w)
        r = next(r for r in p['mappings'] if len(r['hint']['vertices']) > 1)
        r['hint']['vertices'][1] = r['hint']['vertices'][0]
        with self.assertRaises(ValueError): f.validate(p)

    def test_sensitive_node_branch_flip_rejected(self):
        p = deepcopy(w)
        for r in p['mappings']:
            g = f.term(p['raw_hodge_packet'], r['source'])['graph']
            edge = next((e for e in range(len(g['endpoints'])) if
                g['endpoints'][e][0] != g['endpoints'][e][1] or
                g['half_psi'][e][0] != g['half_psi'][e][1]), None)
            if edge is not None:
                r['hint']['swaps'][edge] = not r['hint']['swaps'][edge]
                break
        else: self.fail('Expected a branch-sensitive graph')
        with self.assertRaises(ValueError): f.validate(p)

    def test_raw_coefficient_or_flag_map_change_rejected(self):
        for change in ['coefficient', 'admcycles_flag_map']:
            p = deepcopy(w);p['mappings'][0][change][0] = 999
            with self.assertRaises(ValueError): f.validate(p)

    def test_preservation_includes_all_kappa_indices_and_external_psi(self):
        r = w['mappings'][0]
        g = f.term(w['raw_hodge_packet'], r['source'])['graph']
        h = f.term(w['raw_hodge_packet'], w['representatives'][r['representative_index']][
            'source_reference'])['graph']
        for changed in ['kappa', 'leg_psi']:
            bad = deepcopy(h)
            if changed == 'kappa': bad['kappa'][r['hint']['vertices'][0]][3] += 1
            else: bad['leg_psi'][0] += 1
            with self.assertRaises(ValueError): f.hint_valid(g, bad, r['hint'])

    def test_grouped_coordinate_change_rejected(self):
        p = deepcopy(w);p['representatives'][0]['left_coefficient'] = [999, 1]
        with self.assertRaises(ValueError): f.validate(p)

    def test_embedded_raw_packet_change_rejected(self):
        p = deepcopy(w)
        p['raw_hodge_packet']['pairs'][0]['components'][0]['terms'][0]['coefficient'] = [2, 1]
        with self.assertRaises(ValueError): f.validate(p)

    def test_unchanged_raw_normalization_and_false_acceptance(self):
        self.assertEqual(w['normalization'], 'raw_gluing_pushforward')
        self.assertTrue(all(v is False for v in w['claims'].values()))
        self.assertFalse(any(k == 'sage' or k.startswith('sage.') or
            k == 'admcycles' or k.startswith('admcycles.') for k in sys.modules))

    def test_exact_public_source_and_consumer_replay(self):
        source, bindings, audit, checks = f.prepare()
        self.assertEqual(source, PRODUCTION.read_text())
        self.assertEqual(f.consumer_source(), CONSUMER.read_text())
        self.assertEqual(len(bindings), 230)
        self.assertEqual(len({b['isomorphism_theorem'] for b in bindings}), 111)
        self.assertEqual(len(audit), 122)
        self.assertEqual(len(set(audit)), 122)
        self.assertEqual(checks['exact_grouped_difference'], 0)

    def test_no_search_helpers_or_heavy_runtime_loaded(self):
        f.prepare()
        for name in ['search_belorousski_pandharipande', 'export_l24_initial',
                     'sage', 'admcycles']:
            self.assertFalse(any(n == name or n.startswith(name + '.') for n in sys.modules))

    def test_changed_decoder_rejected_before_execution(self):
        with tempfile.TemporaryDirectory(prefix='hodge-iso-helper-test-') as directory:
            root = Path(directory)
            sentinel = root / 'executed'
            helper = root / 'decoder.py'
            helper.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            with self.assertRaisesRegex(ValueError, 'Changed reviewed input'):
                f.load(helper, '0' * 64, 'must_not_execute')
            self.assertFalse(sentinel.exists())

    def test_changed_independent_input_pins_rejected(self):
        for input_name in ['raw_path', 'witness_path', 'raw_lean_path']:
            with self.subTest(input_name=input_name):
                with tempfile.TemporaryDirectory(prefix='hodge-iso-pin-test-') as directory:
                    changed = Path(directory) / 'changed'
                    original = {'raw_path': f.RAW, 'witness_path': f.WITNESS,
                                'raw_lean_path': f.RAW_LEAN}[input_name]
                    changed.write_bytes(original.read_bytes() + b'\n')
                    with self.assertRaises(ValueError):
                        f.prepare(**{input_name: changed})

    def test_cli_replays_outside_the_repository_and_preserves_existing_outputs(self):
        with tempfile.TemporaryDirectory(prefix='hodge-iso-cli-test-') as directory:
            root = Path(directory)
            production, consumer, ledger = (root / n for n in ['source.lean', 'test.lean', 'ledger.json'])
            command = [sys.executable, str(SCRIPT), '--output', str(production),
                       '--tests', str(consumer), '--ledger', str(ledger)]
            result = subprocess.run(command, cwd=root, text=True, capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(production.read_bytes(), PRODUCTION.read_bytes())
            self.assertEqual(consumer.read_bytes(), CONSUMER.read_bytes())
            data = json.loads(ledger.read_text())
            self.assertFalse(data['lean_executed'])
            self.assertEqual(data['occurrences'], 230)
            self.assertEqual(data['audit_declarations'], 122)
            before = [p.read_bytes() for p in [production, consumer, ledger]]
            retry = subprocess.run(command, cwd=root, text=True, capture_output=True, check=False)
            self.assertNotEqual(retry.returncode, 0)
            self.assertEqual(before, [p.read_bytes() for p in [production, consumer, ledger]])

    def test_colliding_output_files_rejected_before_writing(self):
        with tempfile.TemporaryDirectory(prefix='hodge-iso-alias-test-') as directory:
            production = Path(directory) / 'same.lean'
            ledger = Path(directory) / 'ledger.json'
            result = subprocess.run([sys.executable, str(SCRIPT), '--output', str(production),
                '--tests', str(production), '--ledger', str(ledger)],
                text=True, capture_output=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(production.exists())
            self.assertFalse(ledger.exists())


if __name__ == '__main__':
    unittest.main()

