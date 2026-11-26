"""Check saved actual F1 evidence without opening historical paths or running Lean."""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import types
import zlib

ROOT = Path(__file__).resolve().parents[1]
HELPER = 'scripts/check_f1_root_zero_record.py'
HELPER_SHA = 'fdc46be68d7f1b8b5a523bf01a2f3d47970803c60502a8065f2924f41ba755bb'
FRAME_SHA = '8643038afc27ecf4a5ec0d705a45e7ebf243215d309e6ee7b28edce9f1787ff7'
LEDGER_SHA = [
    '8cc77345ff8ca7d35858f863d19ad1193de5f721728ff1b6a427b4c633c933af',
    'cf7e92d9e5e286810ced537d3fd32407ac28bbded683be5cb2a9b01fecaeb2c5',
    'd8991f5ba3230efa4c50460030a1c021d01828b7f0c22d9fe8cdfd865180dcf6',
]
AUDIT_META_SHA = [
    '5bb8626f7ec8ef1b593cab3b1a453f600078d5f504907ab7012691514786e32e',
    '73d4f9f531d3ef24516528744c4096cb47ccf5e16dcd3c2fa3e44fdd586c4f45',
]
AUDIT_ACCEPTANCE_SHA = [
    '15ce7031833b5c1e9de5ad403d831be90f059de3bddfe6c443e31461d594174e',
    '224af5886f2f7a6e790ed9566f6c066ffaeaafd01ce992fc0b91ffac79f8b33b',
]
MAX_BLOB = 32 * 1024**2
MAX_TOTAL = 96 * 1024**2
CONFIG = {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'Duplicate JSON field')
        result[key] = value
    return result


def loads(raw):
    return json.loads(raw, object_pairs_hook=unique)


def relative(repository, path):
    need(isinstance(path, str) and '\\' not in path, 'Invalid relative path')
    value = Path(path)
    need(not value.is_absolute() and '..' not in value.parts and str(value) == path,
         'Noncanonical relative path')
    result = repository / value
    need(result.resolve().is_relative_to(repository.resolve()), 'Path escapes repository')
    return result


def load_helper(repository):
    path = relative(repository, HELPER)
    raw = path.read_bytes()
    need(sha(raw) == HELPER_SHA, 'Parser/lexer changed before execution')
    helper = types.ModuleType('verified_f1_parser')
    helper.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), helper.__dict__)
    return helper


class Blobs:
    """Decode each full file once, with strict size, stream and digest bounds."""
    def __init__(self, table):
        need(isinstance(table, dict) and len(table) <= 1200, 'Invalid blob table size')
        self.table, self.cache, self.total = table, {}, 0

    def get(self, reference):
        digest = reference['sha256']
        need(re.fullmatch('[0-9a-f]{64}', digest), 'Invalid blob digest')
        if digest not in self.cache:
            row = self.table[digest]
            size = row['decoded_bytes']
            need(type(size) is int and 0 <= size <= MAX_BLOB, 'Invalid decoded blob size')
            need(row['encoding'] == 'zlib-base64', 'Unsupported blob encoding')
            need(isinstance(row['data'], str) and len(row['data']) <= MAX_BLOB * 2,
                 'Encoded blob too large')
            packed = base64.b64decode(row['data'], validate=True)
            decoder = zlib.decompressobj()
            raw = decoder.decompress(packed, size + 1)
            need(len(raw) == size and decoder.eof and not decoder.unconsumed_tail and
                 not decoder.unused_data, 'Invalid bounded compressed stream')
            need(sha(raw) == digest, 'Decoded blob digest differs')
            self.total += size
            need(self.total <= MAX_TOTAL, 'Decoded evidence exceeds total limit')
            self.cache[digest] = raw
        return self.cache[digest]

    def json(self, reference):
        return loads(self.get(reference))


def warning_blocks(text):
    blocks = re.findall(r'(?ms)^warning: .*?^Note: This linter can be disabled with `[^\n]+`', text)
    need(len(blocks) == len(re.findall(r'(?m)^warning: ', text)), 'Unclassified warning format')
    return blocks


def check_record(record, repository=ROOT, allow_unfinalized=False):
    repository = Path(repository)
    helper = load_helper(repository)
    need(type(record['schema_version']) is int and record['schema_version'] == 1, 'Wrong schema')
    need(record['kind'] == 'f1_actual_cache_and_selected_rows', 'Wrong scope kind')
    need(record['status'] == 'actual235_builds_and2505_audits_passed', 'Acceptance incomplete')
    need(record['frame']['sha256'] == FRAME_SHA, 'Exact scope frame changed')
    blobs = Blobs(record['blobs'])
    frame = blobs.json(record['frame'])
    configs = frame['configuration']
    need(len(configs) == 3 and {x['path'] for x in configs} == CONFIG, 'Exact config frame required')
    for row in configs:
        need(sha(relative(repository, row['path']).read_bytes()) == row['sha256'], 'Configuration drift')
    source = frame['source_closure']
    modules = source['modules']
    need(len(modules) == source['module_count'] == 582, 'Source count differs')
    need([x['module'] for x in modules] == source['import_order'], 'Source order differs')
    bymodule, bypath, seen, external = {}, {}, set(), set()
    for row in modules:
        module = row['module']
        need(row['path'] == module.replace('.', '/') + '.lean', 'Noncanonical module path')
        need(module not in seen, 'Duplicate source module')
        raw = relative(repository, row['path']).read_bytes()
        need(sha(raw) == row['sha256'], 'Source drift')
        need(helper.lean_imports(raw.decode()) == row['imports'], 'Lexical import drift')
        for name in row['imports']:
            if name.startswith(('AxiomaticGW.', 'AxiomaticGWTest.')):
                need(name in seen, 'Non-topological project closure')
            else:
                external.add(name)
        seen.add(module)
        bymodule[module] = row
        bypath[row['path']] = raw.decode().splitlines()
    need(sorted(external) == source['external_imports'], 'External import frame differs')
    need(set(source['roots']) <= seen, 'Missing source root')
    need(len(record['ledgers']) == 3, 'Exact three ledger phases required')
    ledgers = []
    for ref, expected in zip(record['ledgers'], LEDGER_SHA):
        need(ref['sha256'] == expected, 'Authoritative ledger pin changed')
        ledgers.append(blobs.json(ref))
    first, resumed, post = ledgers
    need(first['status'] == 'stopped_at_failure' and len(first['steps']) == 22, 'Missing RSS history')
    need(resumed['status'] == 'all227_repository_targets_passed_audit_and_warning_review_pending',
         '227-target continuation incomplete')
    need(post['status'] == 'all8_repository_targets_passed_audit_and_warning_review_pending',
         'Eight-target phase incomplete')
    need(resumed['reused_passed_steps'] == first['steps'][:21], 'Reused prefix differs')
    steps = first['steps'][:21] + resumed['steps'] + post['steps']
    targets = frame['original_targets'] + frame['post_targets']
    need(len(steps) == len(record['runs']) == len(targets) == 235, 'Build coverage differs')
    need([step['module'] for step in steps] == targets, 'Target order differs')
    need(first['module_order'] == resumed['module_order'] == frame['original_targets'], '227 order differs')
    warning_counts, warnings_seen = {}, {}
    total_warning_occurrences = 0

    def classify(block):
        if block in warnings_seen:
            return warnings_seen[block]
        match = re.fullmatch(r'warning: ([^:\n]+):(\d+):(\d+): (.*)', block, re.S)
        need(match is not None, 'Warning lacks source coordinate')
        path, line, column, body = match.groups()
        need(path in bypath and 1 <= int(line) <= len(bypath[path]), 'Warning source outside closure')
        actual = bypath[path][int(line) - 1]
        kind = re.search(r'`set_option (linter\.style\.[A-Za-z]+) false`$', body)
        need(kind is not None, 'Unknown warning category')
        category = kind.group(1)
        if category == 'linter.style.maxHeartbeats':
            need(body.startswith('Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in\n')
                 and re.fullmatch(r'\s*set_option maxHeartbeats \d+ in\s*', actual), 'Heartbeat warning binding')
        elif category == 'linter.style.setOption':
            need(body.startswith('Unscoped option maxHeartbeats is not allowed:\n')
                 and re.fullmatch(r'\s*set_option maxHeartbeats \d+\s*', actual), 'Option warning binding')
        elif category == 'linter.style.longLine':
            need(body.startswith('This line exceeds the 100 character limit, please shorten it!\n')
                 and int(column) == 100 and len(actual) > 100, 'Long-line warning binding')
        else:
            raise ValueError('Unreviewed warning category')
        warnings_seen[block] = category
        return category

    def successful(meta_ref, log_ref, command, timeout, cap, compiling):
        nonlocal total_warning_occurrences
        meta = blobs.json(meta_ref)
        text = blobs.get(log_ref).decode()
        need(meta['log']['sha256'] == log_ref['sha256'], 'Metadata/log pin mismatch')
        need(meta['status'] == 'passed' and meta['exit_code'] == 0, 'Failed command')
        need(meta['command'] == command, 'Unexpected command')
        need(meta['timeout_seconds'] == timeout and meta['rss_limit_bytes'] == cap, 'Resource limits differ')
        need(not meta['violations'], 'Resource violation')
        need(meta['max_sampled_concurrent_lean_children'] == (1 if compiling else 0), 'Unexpected Lean concurrency')
        need(0 <= meta['peak_sampled_lean_rss_bytes'] <= cap, 'RSS observation exceeds cap')
        if compiling:
            need(meta['peak_sampled_lean_rss_bytes'] > 0, 'Missing actual compiler observation')
        need('Build completed successfully' in text or 'All targets up-to-date' in text, 'Missing Lake completion')
        need(not re.search(r'\berror:|sorryAx|memory_exception|declaration uses .sorry.', text), 'Proof diagnostic')
        for block in warning_blocks(text):
            category = classify(block)
            warning_counts[category] = warning_counts.get(category, 0) + 1
            total_warning_occurrences += 1

    for index, (step, run) in enumerate(zip(steps, record['runs'])):
        module = step['module']
        need(step['status'] == 'passed' and run['module'] == module, 'Unaccepted build step')
        need(step['source']['sha256'] == bymodule[module]['sha256'], 'Built source differs')
        need(run['build_metadata'] == step['build'] and run['prerequisite_metadata'] == step['prerequisites'],
             'Build evidence not tied to ledger')
        cap = (2 if index < 21 else 3) * 1024**3
        meta = blobs.json(run['build_metadata'])
        lake = meta['command'][0]
        need(Path(lake).name == 'lake', 'Unexpected build executable')
        successful(run['build_metadata'], run['build_log'],
                   [lake, '--no-ansi', '--no-cache', 'build', module], 120, cap, True)
        imports = bymodule[module]['imports']
        # The original serial driver partitions project/vendor imports; post8 preserves lexical order.
        dependencies = ([n for n in imports if n.startswith(('AxiomaticGW.', 'AxiomaticGWTest.'))] +
                        [n for n in imports if not n.startswith(('AxiomaticGW.', 'AxiomaticGWTest.'))])
        if index >= 227:
            dependencies = imports
        successful(run['prerequisite_metadata'], run['prerequisite_log'],
                   [lake, '--no-ansi', '--no-cache', '--no-build', 'build', *dependencies], 30, cap, False)
    failed = first['steps'][-1]
    need(record['failed_attempt']['metadata'] == failed['build'], 'Lost failed attempt')
    failure = blobs.json(record['failed_attempt']['metadata'])
    need(failure['status'] == 'lean_rss_limit_exceeded' and failure['rss_limit_bytes'] == 2 * 1024**3,
         'Historical failure differs')
    need(failure['log']['sha256'] == record['failed_attempt']['log']['sha256'], 'Failure log pin differs')
    blobs.get(record['failed_attempt']['log'])
    need(record['failed_attempt']['prerequisite_metadata'] == failed['prerequisites'],
         'Failed-attempt prerequisite differs')
    failed_pre = blobs.json(record['failed_attempt']['prerequisite_metadata'])
    need(failed_pre['log']['sha256'] == record['failed_attempt']['prerequisite_log']['sha256'],
         'Failed-attempt prerequisite log differs')
    blobs.get(record['failed_attempt']['prerequisite_log'])
    need(record['historical_successful_rss'] == resumed['historical_successful_RSS'],
         'Previous accepted RSS observation differs')
    previous = blobs.json(record['historical_successful_rss'])
    need(previous['status'] == 'passed' and previous['children_ru_maxrss_raw'] == 2164703232,
         'Previous accepted RSS history differs')
    need(record['source_bound_plan_history'] == list(frame['required_evidence'].values()),
         'Pinned plan history differs')
    for reference in record['source_bound_plan_history']:
        blobs.get(reference)
    need(len(record['audits']) == 2, 'Exact two actual audit runs required')
    audit_results = []
    for index, (audit, key, count) in enumerate(zip(record['audits'],
            ['cache_and_nine_roots', 'rows123_to125'], [2332, 173])):
        need(audit['metadata']['sha256'] == AUDIT_META_SHA[index], 'Actual audit metadata differs')
        plan = frame['audit_frames'][key]
        expected_source = plan['audit'] if index == 0 else plan['source']
        need(audit['source']['sha256'] == expected_source['sha256'] and
             audit['expected']['sha256'] == plan['expected']['sha256'], 'Audit frame differs')
        meta = blobs.json(audit['metadata'])
        need(meta['status'] == 'passed' and meta['exit_code'] == 0, 'Audit command failed')
        need(meta['command'] == ['lake', 'env', 'lean', '--memory=2048', audit['source']['path']],
             'Wrong audit command')
        source_text = blobs.get(audit['source']).decode()
        expected = blobs.json(audit['expected'])
        names = expected if isinstance(expected, list) else expected['names']
        need(len(names) == len(set(names)) == count, 'Audit expected coverage differs')
        need(re.findall(r'^#print axioms (\S+)$', source_text, re.M) == names, 'Audit source names differ')
        parsed = helper.parse_audits(blobs.get(audit['log']).decode())
        need(list(parsed) == names, 'Actual audit coverage/order differs')
        need(audit['root_acceptance']['sha256'] == AUDIT_ACCEPTANCE_SHA[index], 'Root audit acceptance differs')
        acceptance = blobs.json(audit['root_acceptance'])
        need(acceptance['status'] == 'exact_actual_audit_passed' and acceptance['count'] == count and
             acceptance['axioms'] == parsed and acceptance['log_sha256'] == audit['log']['sha256'],
             'Actual audit evidence differs from source-bound root acceptance')
        audit_results.append(parsed)
    need(record['full815_constant_accepted'] is False and record['all414_transfers_accepted'] is False
         and record['geometric_CohFT_accepted'] is False, 'Invented completion claim')
    # Verify every included full file, including provenance not used as a success premise.
    for digest in record['blobs']:
        blobs.get({'sha256': digest})
    summary = {'actual_builds': 235, 'actual_audits': [len(x) for x in audit_results],
               'sources': 582, 'warning_categories': warning_counts,
               'distinct_source_bound_warning_blocks': len(warnings_seen),
               'warning_occurrences_in_passed_builds_and_preflights': total_warning_occurrences,
               'decoded_evidence_bytes': blobs.total,
               'status': 'verified_without_Lean_or_historical_path_reads'}
    need((allow_unfinalized and record['validation_summary'] is None) or
         record['validation_summary'] == summary, 'Stored summary differs')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', type=Path, default=ROOT)
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    path = args.record or args.repository / 'environments/genus-two-f1-actual-cache-validation.json'
    print(json.dumps(check_record(loads(path.read_bytes()), args.repository), indent=2))


if __name__ == '__main__':
    main()
