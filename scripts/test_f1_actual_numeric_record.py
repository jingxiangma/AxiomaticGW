"""Portable corruption controls for the actual cache/selected-row evidence."""
import argparse
import base64
import copy
import importlib.util
import json
from pathlib import Path
import re
import unittest
from unittest.mock import patch
import zlib

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--repository', type=Path, default=HERE.parent)
parser.add_argument('--record', type=Path)
args, test_args = parser.parse_known_args()
args.record = args.record or args.repository / 'environments/genus-two-f1-actual-cache-validation.json'
spec = importlib.util.spec_from_file_location('actual_checker', HERE / 'check_f1_actual_numeric_record.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class ActualRecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = checker.loads(args.record.read_bytes())

    def rejected(self, record, pattern=None):
        if pattern:
            with self.assertRaisesRegex(ValueError, pattern):
                checker.check_record(record, args.repository)
        else:
            with self.assertRaises(ValueError):
                checker.check_record(record, args.repository)

    def changed_blob(self, record, ref, raw):
        digest = checker.sha(raw)
        record['blobs'][digest] = {'encoding': 'zlib-base64', 'decoded_bytes': len(raw),
                                   'data': base64.b64encode(zlib.compress(raw)).decode()}
        ref['sha256'] = digest

    def audit_change(self, transform):
        record = copy.deepcopy(self.record)
        ref = record['audits'][0]['log']
        raw = checker.Blobs(record['blobs']).get(ref).decode()
        self.changed_blob(record, ref, transform(raw).encode())
        self.rejected(record)

    def test_actual_record(self):
        result = checker.check_record(self.record, args.repository)
        self.assertEqual((result['sources'], result['actual_builds'], result['actual_audits']),
                         (582, 235, [2332, 173]))

    def test_no_historical_path_reads(self):
        original = Path.read_bytes
        def guarded(path):
            self.assertTrue(path.resolve().is_relative_to(args.repository.resolve()))
            self.assertFalse('.lake' in path.parts)
            return original(path)
        with patch.object(Path, 'read_bytes', guarded):
            checker.check_record(self.record, args.repository)

    def test_missing_config_cannot_be_rehashed(self):
        record = copy.deepcopy(self.record)
        frame = checker.Blobs(record['blobs']).json(record['frame'])
        frame['configuration'] = []
        self.changed_blob(record, record['frame'], json.dumps(frame).encode())
        self.rejected(record, 'Exact scope frame')

    def test_source_corruption(self):
        original = Path.read_bytes
        target = args.repository / 'AxiomaticGW/Combinatorics/StableArity.lean'
        def changed(path):
            raw = original(path)
            return raw + b'\n' if path == target else raw
        with patch.object(Path, 'read_bytes', changed):
            self.rejected(self.record, 'Source drift')

    def test_removed_build(self):
        record = copy.deepcopy(self.record)
        record['runs'].pop()
        self.rejected(record, 'Build coverage')

    def test_reordered_build(self):
        record = copy.deepcopy(self.record)
        record['runs'][0], record['runs'][1] = record['runs'][1], record['runs'][0]
        self.rejected(record, 'Unaccepted build step')

    def test_forged_build_success_metadata(self):
        record = copy.deepcopy(self.record)
        ref = record['runs'][0]['build_metadata']
        metadata = checker.Blobs(record['blobs']).json(ref)
        metadata['exit_code'] = 1
        self.changed_blob(record, ref, json.dumps(metadata).encode())
        self.rejected(record, 'not tied to ledger')

    def test_forgotten_audit_phase(self):
        record = copy.deepcopy(self.record)
        record['audits'].pop()
        self.rejected(record, 'Exact two actual audit')

    def test_missing_audit(self):
        self.audit_change(lambda text: re.sub(r"'[^']+' depends on axioms:\s*\[[^\]]*\]\s*", '', text, count=1))

    def test_duplicate_audit(self):
        self.audit_change(lambda text: text + re.search(r"'[^']+' depends on axioms:\s*\[[^\]]*\]", text)[0] + '\n')

    def test_foreign_axiom(self):
        self.audit_change(lambda text: text.replace('propext', 'FakeGeometricInput', 1))

    def test_hidden_diagnostic(self):
        self.audit_change(lambda text: text + 'warning: unreviewed proof output\n')

    def test_corrupt_compressed_bytes(self):
        record = copy.deepcopy(self.record)
        blob = record['blobs'][record['frame']['sha256']]
        blob['data'] = 'not base64!'
        with self.assertRaises((ValueError, zlib.error)):
            checker.check_record(record, args.repository)

    def test_bounded_decompression_rejects_understated_size(self):
        raw = b'a' * 100000
        digest = checker.sha(raw)
        blob = {'encoding': 'zlib-base64', 'decoded_bytes': 1,
                'data': base64.b64encode(zlib.compress(raw)).decode()}
        with self.assertRaisesRegex(ValueError, 'bounded compressed stream'):
            checker.Blobs({digest: blob}).get({'sha256': digest})

    def test_appended_compressed_stream_rejected(self):
        raw = b'{}'
        digest = checker.sha(raw)
        blob = {'encoding': 'zlib-base64', 'decoded_bytes': len(raw),
                'data': base64.b64encode(zlib.compress(raw) + zlib.compress(raw)).decode()}
        with self.assertRaisesRegex(ValueError, 'bounded compressed stream'):
            checker.Blobs({digest: blob}).get({'sha256': digest})

    def test_oversize_declared_blob_rejected_before_decode(self):
        digest = '0' * 64
        blob = {'encoding': 'zlib-base64', 'decoded_bytes': checker.MAX_BLOB + 1, 'data': ''}
        with self.assertRaisesRegex(ValueError, 'decoded blob size'):
            checker.Blobs({digest: blob}).get({'sha256': digest})

    def test_missing_ledger_rejected(self):
        record = copy.deepcopy(self.record)
        record['ledgers'].pop()
        self.rejected(record, 'Exact three ledger')

    def test_cannot_accept_full_constant_or_geometry(self):
        for field in ['full815_constant_accepted', 'all414_transfers_accepted', 'geometric_CohFT_accepted']:
            record = copy.deepcopy(self.record)
            record[field] = True
            self.rejected(record, 'Invented completion')

    def test_duplicate_json_keys(self):
        with self.assertRaisesRegex(ValueError, 'Duplicate JSON'):
            checker.loads('{"schema_version":1,"schema_version":2}')

    def test_paths_cannot_escape(self):
        for name in ['/tmp/forged', '../forged', './lakefile.toml']:
            with self.assertRaises(ValueError):
                checker.relative(args.repository, name)


if __name__ == '__main__':
    unittest.main(argv=['test_f1_actual_numeric_record.py'] + test_args)
