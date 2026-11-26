#!/usr/bin/env python3
"""Pure offline checks for raw Hodge-strata export and Lean syntax replay.

These tests never import Sage/admcycles or invoke Lean. The frozen public
Lean sources are compared byte-for-byte, including every raw coefficient
and every occurrence. Kernel acceptance is a separate build check.
"""

import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/export_admcycles_hodge_certificate.py'
RAW = ROOT / 'environments/admcycles-hodge-strata-candidates.json'
PRODUCTION = ROOT / 'AxiomaticGW/GKM/Fixtures/AdmcyclesHodgeStrataCandidates.lean'
CONSUMERS = ROOT / 'AxiomaticGWTest/GKM/AdmcyclesHodgeStrataCandidates.lean'

spec = importlib.util.spec_from_file_location('hodge_certificate_under_test', SCRIPT)
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)


class HodgeCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.shared, cls.source = exporter.dependencies()
        cls.packet = json.loads(RAW.read_text(), object_pairs_hook=cls.shared.unique_object)
        exporter.validate_packet(cls.packet, cls.shared, cls.source)

    def test_frozen_input_and_every_occurrence_replay_exactly(self):
        self.assertEqual(exporter.digest(RAW), exporter.INPUT_SHA256)
        text, graphs, incidences, mappings = exporter.emit(self.packet, self.shared)
        self.assertEqual(text, PRODUCTION.read_text())
        self.assertEqual(exporter.consumer_source(), CONSUMERS.read_text())
        self.assertEqual((len(graphs), len(incidences), len(mappings)), (373, 61, 553))
        self.assertEqual(len(self.packet['pairs']), 9)
        self.assertEqual(sum(len(p['components']) for p in self.packet['pairs']), 45)
        counts = [sum(len(c['terms']) for c in p['components']) for p in self.packet['pairs']]
        self.assertEqual(counts, [1, 5, 16, 5, 28, 122, 16, 108, 252])
        for mapping in mappings:
            pair_index = 3 * mapping['pair'][0] + mapping['pair'][1]
            term = self.packet['pairs'][pair_index]['components'][mapping['degree']]['terms'][mapping['term']]
            self.assertEqual(mapping['coefficient'], term['coefficient'])
            self.assertEqual(mapping['source_halfedge_labels'], term['graph']['admcycles_halfedge_labels'])
            index = int(mapping['graph_declaration'].removeprefix('rawGraph'))
            self.assertEqual(exporter.graph_key(graphs[index]), exporter.graph_key(term['graph']))

    def test_source_imports_do_not_load_sage_or_admcycles(self):
        self.assertFalse(any(n == 'sage' or n.startswith('sage.') or
                             n == 'admcycles' or n.startswith('admcycles.') for n in sys.modules))

    def test_recorded_semantic_mutations_are_rejected(self):
        results = exporter.mutation_checks(self.packet, self.shared, self.source)
        self.assertEqual(len(results), 7)
        self.assertTrue(all(r['rejected'] for r in results))

    def test_graph_data_mutations_are_rejected(self):
        base = next(t['graph'] for p in self.packet['pairs'] for c in p['components']
                    for t in c['terms'] if t['graph']['endpoints'])
        mutations = [
            lambda g: g['half_psi'][0].__setitem__(0, -1),
            lambda g: g['admcycles_halfedge_labels'][0].__setitem__(0, 1),
            lambda g: g['admcycles_halfedge_labels'][0].__setitem__(1, g['admcycles_halfedge_labels'][0][0]),
            lambda g: g['endpoints'][0].__setitem__(0, len(g['genus'])),
            lambda g: g['kappa'][0].append(0),
            lambda g: g['genus'].__setitem__(0, True),
        ]
        for mutate in mutations:
            graph = copy.deepcopy(base)
            mutate(graph)
            with self.assertRaises(ValueError):
                self.source.validate_graph(graph)

    def test_exact_ordered_branches_and_decorations_affect_graph_key(self):
        base = next(t['graph'] for p in self.packet['pairs'] for c in p['components']
                    for t in c['terms'] if t['graph']['endpoints'])
        for field, at in [('kappa', (0, 0)), ('half_psi', (0, 0))]:
            changed = copy.deepcopy(base)
            changed[field][at[0]][at[1]] += 1
            self.assertNotEqual(exporter.graph_key(changed), exporter.graph_key(base))
        changed = copy.deepcopy(base)
        changed['leg_psi'][0] += 1
        self.assertNotEqual(exporter.graph_key(changed), exporter.graph_key(base))
        renamed = copy.deepcopy(base)
        renamed['admcycles_halfedge_labels'] = [[h + 100 for h in edge]
                                               for edge in base['admcycles_halfedge_labels']]
        self.assertEqual(exporter.graph_key(renamed), exporter.graph_key(base))

    def test_duplicate_json_object_keys_rejected(self):
        with self.assertRaises(ValueError):
            json.loads('{"schema_version":1,"schema_version":1}',
                       object_pairs_hook=self.shared.unique_object)

    def test_changed_helper_is_rejected_before_execution(self):
        with tempfile.TemporaryDirectory(prefix='hodge-pin-test-') as directory:
            root = Path(directory)
            sentinel = root / 'executed'
            helper = root / 'helper.py'
            helper.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            with self.assertRaisesRegex(ValueError, 'Changed helper source'):
                exporter.load(helper, 'must_not_execute', '0' * 64)
            self.assertFalse(sentinel.exists())

    def test_raw_export_checks_source_pins_before_helper_execution(self):
        with tempfile.TemporaryDirectory(prefix='hodge-source-pin-test-') as directory:
            root = Path(directory)
            scripts = root / 'scripts'
            scripts.mkdir()
            sentinel = root / 'executed'
            helper = scripts / 'export_admcycles_certificate.py'
            helper.write_text(f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            installed = root / 'admcycles'
            installed.mkdir()
            (installed / 'tautological_ring.py').write_text('# changed installed source\n')
            with patch.object(self.source, 'installed_admcycles_directory', return_value=installed):
                with self.assertRaisesRegex(ValueError, 'Source pin changed'):
                    self.source.deferred_export(root)
            self.assertFalse(sentinel.exists())

    def test_package_discovery_does_not_execute_admcycles(self):
        with tempfile.TemporaryDirectory(prefix='hodge-discovery-test-') as directory:
            root = Path(directory)
            package = root / 'admcycles'
            package.mkdir()
            sentinel = root / 'executed'
            (package / '__init__.py').write_text(
                f'from pathlib import Path\nPath({str(sentinel)!r}).touch()\n')
            with patch.object(sys, 'path', [str(root)] + sys.path):
                self.assertEqual(self.source.installed_admcycles_directory(), package.resolve())
            self.assertFalse(sentinel.exists())

    def test_cli_replays_from_an_unrelated_working_directory(self):
        with tempfile.TemporaryDirectory(prefix='hodge-offline-replay-') as directory:
            root = Path(directory)
            output, tests, ledger = (root / n for n in ['candidate.lean', 'consumer.lean', 'ledger.json'])
            command = [sys.executable, str(SCRIPT), '--input', str(RAW), '--output', str(output),
                       '--tests', str(tests), '--ledger', str(ledger)]
            result = subprocess.run(command, cwd=root, text=True, capture_output=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(output.read_bytes(), PRODUCTION.read_bytes())
            self.assertEqual(tests.read_bytes(), CONSUMERS.read_bytes())
            record = json.loads(ledger.read_text())
            self.assertEqual(record['raw_terms'], 553)
            self.assertFalse(record['lean_validation']['run'])
            self.assertEqual(record['accepted_geometric_claims'], [])
            before = [p.read_bytes() for p in [output, tests, ledger]]
            repeated = subprocess.run(command, cwd=root, text=True, capture_output=True, check=False)
            self.assertNotEqual(repeated.returncode, 0)
            self.assertEqual(before, [p.read_bytes() for p in [output, tests, ledger]])

    def test_colliding_outputs_are_rejected_before_writing(self):
        with tempfile.TemporaryDirectory(prefix='hodge-output-alias-test-') as directory:
            shared_path = Path(directory) / 'collision.lean'
            ledger = Path(directory) / 'ledger.json'
            result = subprocess.run([sys.executable, str(SCRIPT), '--input', str(RAW),
                '--output', str(shared_path), '--tests', str(shared_path), '--ledger', str(ledger)],
                text=True, capture_output=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(shared_path.exists())
            self.assertFalse(ledger.exists())

    def test_changed_input_pin_rejected_before_outputs(self):
        with tempfile.TemporaryDirectory(prefix='hodge-input-pin-test-') as directory:
            root = Path(directory)
            changed = root / 'changed.json'
            changed.write_bytes(RAW.read_bytes() + b'\n')
            output, tests, ledger = (root / n for n in ['candidate.lean', 'consumer.lean', 'ledger.json'])
            result = subprocess.run([sys.executable, str(SCRIPT), '--input', str(changed),
                '--output', str(output), '--tests', str(tests), '--ledger', str(ledger)],
                text=True, capture_output=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(any(p.exists() for p in [output, tests, ledger]))


if __name__ == '__main__':
    unittest.main()
