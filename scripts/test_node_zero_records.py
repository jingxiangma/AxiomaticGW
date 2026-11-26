"""Corruption controls for actual node/zero records; no Lean or repository writes."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--repository', type=Path, default=HERE.parent)
parser.add_argument('--node-record', type=Path)
parser.add_argument('--zero-record', type=Path)
args, unittest_args = parser.parse_known_args()
args.node_record = args.node_record or args.repository / 'environments/gkm-hodge-node-normal-validation.json'
args.zero_record = args.zero_record or args.repository / 'environments/genus-two-f1-root-zero-rows-validation.json'
spec = importlib.util.spec_from_file_location('recorder', HERE / 'check_node_zero_records.py')
recorder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recorder)
helper = recorder.load_helper(args.repository)

def verified(record):
    return recorder.check_record(record, args.repository, helper)


class RecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.node = recorder.load(args.node_record)
        cls.zero = recorder.load(args.zero_record)

    def rejected(self, record, text=None):
        if text is None:
            with self.assertRaises(ValueError):
                verified(record)
        else:
            with self.assertRaisesRegex(ValueError, text):
                verified(record)

    def bad_audit(self, transform):
        r = copy.deepcopy(self.node)
        p = r['actual_combined_audit']['full_log']
        p['text'] = transform(p['text'])
        p['sha256'] = recorder.digest(p['text'].encode())
        self.rejected(r)

    def test_both_actual_records(self):
        self.assertTrue(verified(self.node))
        self.assertTrue(verified(self.zero))

    def test_portable_verification_never_reads_tmp(self):
        original = Path.read_bytes
        def guarded(path):
            self.assertFalse(str(path).startswith(('/tmp/', '/private/tmp/')))
            return original(path)
        with patch.object(Path, 'read_bytes', guarded):
            verified(self.node)
            verified(self.zero)

    def test_missing_audit_rejected_even_after_rehash(self):
        self.bad_audit(lambda text: re.sub(r"'[^']+' depends on axioms:\s*\[[^\]]*\]\s*", '', text, count=1))

    def test_duplicate_audit_rejected(self):
        self.bad_audit(lambda text: text + "'AxiomaticGW.NonseparatingNode.firstPowers_sum' depends on axioms: [propext]\n")

    def test_foreign_axiom_rejected(self):
        self.bad_audit(lambda text: text.replace('propext', 'SubstituteAxiom', 1))

    def test_diagnostic_not_ignored(self):
        self.bad_audit(lambda text: text + 'warning: forged acceptable output\n')

    def test_uncompiled_batch_import_rejected(self):
        r = copy.deepcopy(self.node)
        p = r['actual_combined_audit']['source']
        p['text'] = p['text'].replace('module\n', 'module\npublic import AxiomaticGW.Surfaces.Fixtures.BlowupF1RootRelabelTransfers.Batch00\n', 1)
        p['sha256'] = recorder.digest(p['text'].encode())
        self.rejected(r, 'Combined audit imports')

    def test_lexical_import_omission_rejected(self):
        r = copy.deepcopy(self.node)
        row = next(x for x in r['source_closure']['modules'] if len(x['imports']) > 1)
        row['imports'].pop()
        self.rejected(r, 'Exact lexical imports')

    def test_source_pin_corruption_rejected(self):
        r = copy.deepcopy(self.node)
        r['source_closure']['modules'][0]['sha256'] = '0' * 64
        self.rejected(r, 'Closure source drift')

    def test_failed_command_cannot_be_accepted_by_success_text(self):
        r = copy.deepcopy(self.node)
        r['builds'][0]['metadata']['exit_code'] = 1
        self.rejected(r, 'Build failed')

    def test_wrong_target_rejected(self):
        r = copy.deepcopy(self.node)
        r['builds'][0]['metadata']['command'][-1] = 'AxiomaticGW'
        self.rejected(r, 'Unexpected build command')

    def test_resource_bound_change_rejected(self):
        r = copy.deepcopy(self.node)
        r['builds'][0]['metadata']['rss_limit_bytes'] = 3072 * 1024**2
        self.rejected(r, 'Resource limit changed')

    def test_forged_inherited_warning_rejected(self):
        r = copy.deepcopy(self.zero)
        run = r['builds'][0]
        log = run['full_log']
        log['text'] = log['text'].replace('Please, add a comment', 'Different warning', 1)
        log['sha256'] = recorder.digest(log['text'].encode())
        run['metadata']['log']['sha256'] = log['sha256']
        run['inherited_warning_blocks'] = recorder.warnings(log['text'])
        self.rejected(r, 'New warning')

    def test_incomplete_815_partition_rejected(self):
        r = copy.deepcopy(self.zero)
        rows = r['original_index_partition']['groups']['structural_transfer_targets']
        rows[0] = rows[1]
        self.rejected(r, 'Index partition changed')

    def test_slot_cannot_be_promoted_to_whole_row(self):
        r = copy.deepcopy(self.zero)
        r['whole_row_123_or_124_accepted'] = True
        self.rejected(r, 'Invented complete row')

    def test_cannot_promote_to_full_constant_or_geometry(self):
        for field in ['full815_constant_accepted', 'geometric_CohFT_accepted']:
            r = copy.deepcopy(self.node)
            r[field] = True
            self.rejected(r, 'Invented completion')

    def test_python_failure_rejected(self):
        r = copy.deepcopy(self.zero)
        r['installed_python_validation']['metadata']['exit_code'] = 1
        self.rejected(r, 'Python failed')

    def test_lexer_ignores_comments_and_strings(self):
        source = '/- import False.One /- import False.Two -/ -/\n-- import False.Three\n' \
                 'def note := "import False.Four"\npublic import AxiomaticGW.Real\n'
        self.assertEqual(helper.lean_imports(source), ['AxiomaticGW.Real'])
        with self.assertRaises(ValueError):
            helper.lean_imports('import AxiomaticGW.Real\nimport AxiomaticGW.Real\n')


    def test_schema_version_rejected(self):
        for value in [0, 2, '1', True]:
            r = copy.deepcopy(self.node)
            r['schema_version'] = value
            self.rejected(r, 'Unsupported record schema')

    def test_missing_configuration_rejected(self):
        r = copy.deepcopy(self.node)
        r['configuration'] = []
        self.rejected(r, 'Exact three canonical config')

    def test_duplicate_configuration_rejected(self):
        r = copy.deepcopy(self.node)
        r['configuration'][1] = copy.deepcopy(r['configuration'][0])
        self.rejected(r, 'Exact three canonical config')

    def test_wrong_configuration_path_rejected(self):
        r = copy.deepcopy(self.node)
        r['configuration'][0]['path'] = '/tmp/lakefile.toml'
        self.rejected(r, 'Exact three canonical config')

    def test_module_path_alias_rejected(self):
        r = copy.deepcopy(self.node)
        r['source_closure']['modules'][0]['path'] = './' + r['source_closure']['modules'][0]['path']
        self.rejected(r, 'Module path is not canonical')

    def test_unknown_scope_kind_rejected(self):
        r = copy.deepcopy(self.node)
        r['kind'] = 'something_else'
        self.rejected(r, 'Unknown scope kind')

    def test_missing_external_import_rejected(self):
        r = copy.deepcopy(self.node)
        r['source_closure']['external_imports'].pop()
        self.rejected(r, 'External import union differs')

    def test_spurious_external_import_rejected(self):
        r = copy.deepcopy(self.node)
        r['source_closure']['external_imports'].append('Mathlib.Forged')
        self.rejected(r, 'External import union differs')

    def test_recorded_order_mismatch_rejected(self):
        r = copy.deepcopy(self.node)
        r['source_closure']['import_order'].reverse()
        self.rejected(r, 'Recorded import order differs')

    def test_non_topological_order_rejected(self):
        r = copy.deepcopy(self.node)
        r['source_closure']['import_order'].reverse()
        r['source_closure']['modules'].reverse()
        self.rejected(r, 'not dependency ordered')

    def test_supporting_pin_omission_rejected(self):
        r = copy.deepcopy(self.zero)
        r['supporting_repository_sources'].pop()
        self.rejected(r, 'Supporting source frame')

    def test_relative_paths_cannot_escape_repository(self):
        for value in ['/tmp/forged', '../forged', 'scripts/../../forged']:
            with self.assertRaises(ValueError):
                recorder.repository_path(args.repository, value)

    def test_duplicate_json_field_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON'):
            json.loads('{"kind":"node_normal","kind":"zero_rows"}', object_pairs_hook=recorder.unique)


if __name__ == '__main__':
    unittest.main(argv=['test_node_zero_records.py'] + unittest_args)
