#!/usr/bin/env python3
"""Regressions for portable cache evidence and its component-only scope."""
import copy
import os
from pathlib import Path
import unittest
from unittest.mock import patch

import check_f1_component_cache_record as C


class RecordChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # The same tests work in the repository after the staged files are copied.
        cls.root = Path(os.environ.get('AXIOMATIC_GW_TEST_ROOT', Path(__file__).resolve().parents[1]))
        cls.record_path = Path(__file__).resolve().parents[1] / 'environments/genus-two-f1-h-component-cache-validation.json'
        cls.record = C.load(cls.record_path.read_bytes())
        cls.closure = C.payload(cls.record_path.parent, cls.record['source_closure'])
        cls.evidence = C.payload(cls.record_path.parent, cls.record['offline_evidence'])

    def changed(self, section, edit, message):
        record, closure, evidence = map(copy.deepcopy, (self.record, self.closure, self.evidence))
        edit({'record': record, 'closure': closure, 'evidence': evidence}[section])
        with self.assertRaisesRegex(ValueError, message):
            C.validate(record, closure, evidence, self.root)

    def test_complete_stored_evidence(self):
        result = C.check(self.record_path, self.root)
        self.assertEqual(result['cache_audits'], 2170)
        self.assertFalse(result['actual_repository_build'])
        self.assertFalse(result['full_contraction_accepted'])

    def test_original_temporary_files_and_oleans_are_not_read(self):
        allowed = {self.record_path.resolve(),
                   (self.record_path.parent / self.record['source_closure']['path']).resolve(),
                   (self.record_path.parent / self.record['offline_evidence']['path']).resolve()}
        allowed |= {(self.root / row['path']).resolve() for row in
                    self.closure['project_sources'] + self.closure['direct_external_sources'] + self.closure['environment']}
        original = Path.read_bytes
        def guarded(path):
            self.assertIn(path.resolve(), allowed)
            self.assertNotEqual(path.suffix, '.olean')
            return original(path)
        with patch.object(Path, 'read_bytes', guarded):
            C.check(self.record_path, self.root)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
            C.load('{"schema_version":1,"schema_version":1}')

    def test_bool_schema_rejected(self):
        self.changed('record', lambda x: x.update(schema_version=True), 'integer')

    def test_bool_count_rejected(self):
        self.changed('record', lambda x: x['counts'].update(components=True), 'integer')

    def test_contraction_acceptance_rejected(self):
        self.changed('record', lambda x: x['acceptance'].update(full_815_contraction=True), 'Unsupported mathematical')

    def test_repository_build_acceptance_rejected(self):
        self.changed('record', lambda x: x['acceptance'].update(actual_repository_build=True), 'Unsupported mathematical')

    def test_curve_change_rejected(self):
        self.changed('record', lambda x: x['query'].update(source_curve=[2]), 'Changed query')

    def test_label_encoding_change_rejected(self):
        self.changed('record', lambda x: x['key_encoding']['labels'].update(point=2), 'Changed full-key')

    def test_source_drift_rejected(self):
        self.changed('closure', lambda x: x['project_sources'][0].update(sha256='0' * 64), 'Source hash mismatch')

    def test_import_cycle_rejected(self):
        self.changed('closure', lambda x: x['project_sources'][-1]['imports'].append(C.ENTRY), 'Source imports differ')

    def test_missing_import_rejected(self):
        self.changed('closure', lambda x: x['project_sources'][-1]['imports'].append('AxiomaticGW.Missing'), 'Source imports differ')

    def test_extra_dependency_preserving_all_module_reachability_rejected(self):
        # The existing closure stays fully reachable and acyclic. Only binding
        # inventory edges to the pinned source catches this corruption.
        def change(x):
            entry = x['project_sources'][-1]
            name = 'AxiomaticGW.Surfaces.Fixtures.BlowupF1CertifiedPoints'
            self.assertNotIn(name, entry['imports'])
            self.assertIn(name, {row['module'] for row in x['project_sources']})
            entry['imports'].append(name)
        self.changed('closure', change, 'Source imports differ')

    def test_duplicate_recorded_direct_import_rejected(self):
        self.changed('closure', lambda x: x['project_sources'][-1]['imports'].append(
            x['project_sources'][-1]['imports'][0]), 'Invalid source classification/imports')

    def test_unexpected_recorded_direct_external_import_rejected(self):
        self.changed('closure', lambda x: x['project_sources'][-1]['imports'].append(
            x['direct_external_sources'][0]['module']), 'Source imports differ')

    def test_import_parser_ignores_nested_comments_and_strings(self):
        self.assertEqual(C.lean_imports('''/- import False.Outer /- import False.Inner -/ -/
public import A.Real -- import False.Line
def text := "import False.String"
public meta import B.Real C.Real
'''), ['A.Real', 'B.Real', 'C.Real'])

    def test_duplicate_source_direct_import_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate direct Lean import'):
            C.lean_imports('import A.Real\npublic import A.Real\n')

    def test_missing_offline_run_rejected(self):
        self.changed('evidence', lambda x: x['runs'].pop(), 'Incomplete offline runs')

    def test_failed_offline_command_rejected(self):
        self.changed('evidence', lambda x: x['runs'][0]['commands'][0].update(exit_code=1), 'Failed offline command')

    def test_bool_offline_exit_rejected(self):
        self.changed('evidence', lambda x: x['runs'][0].update(exit_code=False), 'integer')

    def test_memory_cap_change_rejected(self):
        def change(x):
            row = x['runs'][0]['commands'][0]['command']
            row[row.index('--memory=2048')] = '--memory=8192'
        self.changed('evidence', change, 'memory cap')

    def test_missing_cache_declaration_rejected(self):
        self.changed('evidence', lambda x: x['runs'][0]['audited_declarations'].pop(), 'Run audit names')

    def test_nonstandard_axiom_rejected_even_with_updated_hash(self):
        def change(x):
            old = x['runs'][0]['audit_transcript']
            body = x['audit_transcripts'].pop(old).replace('Quot.sound', 'sorryAx')
            new = C.digest(body.encode())
            x['audit_transcripts'][new] = body
            x['runs'][0]['audit_transcript'] = new
        self.changed('evidence', change, 'Nonstandard axiom')

    def test_historical_failure_cannot_be_promoted(self):
        self.changed('evidence', lambda x: x['historical_failed_runs'][0].update(status='passed'), 'Failure promoted')

    def test_trr_terms_cannot_be_omitted(self):
        self.changed('evidence', lambda x: x['supporting_trr_runs'][0].update(retained_trr_terms=30), 'TRR term coverage')

    def test_trr_part_audit_cannot_be_omitted_with_updated_hash(self):
        def change(x):
            run = x['supporting_trr_runs'][0]
            old = run['audit_transcript']
            body = x['audit_transcripts'].pop(old)
            body = '\n'.join(match.group(0) for match in C.AUDIT.finditer(body)
                             if not match.group(1).endswith('.part_0_eq_zero')) + '\n'
            new = C.digest(body.encode())
            x['audit_transcripts'][new] = body
            run['audit_transcript'] = new
        self.changed('evidence', change, 'Incomplete exact TRR part audits')

    def test_sidecar_path_escape_rejected(self):
        pin = dict(self.record['source_closure'], path='../elsewhere.json.gz')
        with self.assertRaisesRegex(ValueError, 'Invalid relative path'):
            C.payload(self.record_path.parent, pin)


if __name__ == '__main__':
    unittest.main(verbosity=2)
