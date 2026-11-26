"""Verify actual414 structural transfers using the existing bounded evidence utilities."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import types

ROOT = Path(__file__).resolve().parents[1]
UTIL = 'scripts/check_f1_actual_numeric_record.py'
UTIL_SHA = 'fe8c4f9d8d67a8557d69e0e51aa3cb0da9515cc9aba762964d9d11e0d4203208'
PINS = {
    'plan': '835059cb21b2aa686ca5727e6592179db34f898e2e4eda18c7b7d42adc3ab149',
    'ledger': 'f83f3e5cfde3358deb85020d38c2830fe6aa5db64fa7f8cc194c8ec7b7b2193f',
    'warnings': '253b0d4c686e789d9925bc9811e4cbee038ed52a18df61655b8343e2d56c9dcf',
    'audit_metadata': 'c312c7952b89e4c2aeb4b4da1dd9efd9f2f8faf9550c43bceded6b3e229a7860',
    'audit_acceptance': 'fda9d7edd90077d2437698756cfe4707009574c5a9d3304c46329456092903f5',
    'isolated_acceptance': '8b77b4c22b8e99f55fcb1ddf3bffdcd424c1dc86d2d3ab6914488929a5a3b5ba',
    'isolated_ledger': '10d48827abb7fe0c44d53f95d4d03800952a1573d29a52bffaf7e2f9087fecfa',
}


def utilities(repository):
    path = repository / UTIL
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != UTIL_SHA:
        raise ValueError('Evidence utilities changed before execution')
    module = types.ModuleType('verified_bounded_evidence')
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def check(record, repository=ROOT):
    repository = Path(repository)
    u = utilities(repository)
    need, blobs = u.need, u.Blobs(record['blobs'])
    parser = u.load_helper(repository)
    need(type(record['schema_version']) is int and record['schema_version'] == 1, 'Wrong schema')
    need(record['status'] == 'actual17targets_414transfers_2275audits_passed', 'Wrong acceptance status')
    need(set(record['evidence']) == set(PINS), 'Evidence frame incomplete')
    evidence = {}
    for key, expected in PINS.items():
        need(record['evidence'][key]['sha256'] == expected, 'Pinned evidence differs')
        evidence[key] = blobs.json(record['evidence'][key])
    plan, ledger, review = [evidence[key] for key in ['plan', 'ledger', 'warnings']]
    need(plan['target_count'] == 17 and plan['transfer_count'] == 414 and plan['audit_count'] == 2275,
         'Plan counts differ')
    config = plan['configuration']
    need(len(config) == 3 and {row['path'] for row in config} == u.CONFIG, 'Canonical config frame required')
    for row in config:
        need(u.sha(u.relative(repository, row['path']).read_bytes()) == row['sha256'], 'Config drift')
    closure = plan['source_closure']
    need(len(closure['modules']) == closure['module_count'] == 301, 'Closure count differs')
    seen, external, bymodule = set(), set(), {}
    for row in closure['modules']:
        need(row['path'] == row['module'].replace('.', '/') + '.lean', 'Noncanonical source path')
        raw = u.relative(repository, row['path']).read_bytes()
        need(u.sha(raw) == row['sha256'], 'Source changed')
        need(parser.lean_imports(raw.decode()) == row['imports'], 'Lexical imports changed')
        for name in row['imports']:
            if name.startswith(('AxiomaticGW.', 'AxiomaticGWTest.')):
                need(name in seen, 'Dependency order differs')
            else:
                external.add(name)
        need(row['module'] not in seen, 'Duplicate source')
        seen.add(row['module'])
        bymodule[row['module']] = row
    need(closure['import_order'] == list(bymodule) and closure['external_imports'] == sorted(external),
         'Closure order or external union differs')
    need({r['module']: r for r in ledger['source_closure']} == bymodule, 'Built source closure differs')
    need(ledger['status'] == 'all17_actual_targets_passed_audit_and_warning_review_pending', 'Build ledger failed')
    need(len(record['runs']) == len(ledger['steps']) == 17, 'Build frame incomplete')
    need([row['module'] for row in ledger['steps']] == plan['build_order'] == closure['roots'], 'Build order differs')
    baseline = review['warning_blocks']
    need(len(baseline) == 51 and review['status'] == 'all34logs_match_frozen51_warning_multiset', 'Warning reference differs')
    order_changes, elapsed = 0, 0
    for step, run in zip(ledger['steps'], record['runs']):
        module = step['module']
        need(step['status'] == 'passed' and run['module'] == module, 'Unaccepted target')
        need(step['source']['sha256'] == bymodule[module]['sha256'], 'Built source pin differs')
        for key, timeout, children in [('prerequisites', 30, 0), ('build', 120, 1)]:
            need(run[key]['metadata'] == step[key], 'Run differs from source ledger')
            meta = blobs.json(run[key]['metadata'])
            text = blobs.get(run[key]['log']).decode()
            need(meta['log']['sha256'] == run[key]['log']['sha256'], 'Run log differs')
            suffix = (['--no-build', 'build', *bymodule[module]['imports']] if key == 'prerequisites'
                      else ['build', module])
            need(Path(meta['command'][0]).name == 'lake' and
                 meta['command'][1:] == ['--no-ansi', '--no-cache', *suffix], 'Command differs')
            need(meta['status'] == 'passed' and meta['exit_code'] == 0 and not meta['violations'], 'Command failed')
            need(meta['timeout_seconds'] == timeout and meta['rss_limit_bytes'] == 3 * 1024**3 and
                 meta['max_sampled_concurrent_lean_children'] == children and
                 0 <= meta['peak_sampled_lean_rss_bytes'] <= meta['rss_limit_bytes'], 'Resource evidence differs')
            if children:
                need(meta['peak_sampled_lean_rss_bytes'] > 0, 'Missing compiler observation')
                elapsed += meta['elapsed_seconds']
            need(not re.search(r'\berror:|sorryAx|memory_exception', text) and
                 ('Build completed successfully' in text or 'All targets up-to-date' in text), 'Build diagnostic')
            blocks = u.warning_blocks(text)
            need(Counter(blocks) == Counter(baseline), 'Warning multiset differs')
            order_changes += blocks != baseline
    need(order_changes == review['logs_with_different_emission_order'] == 1, 'Warning emission-order evidence differs')
    audit = record['audit']
    for key in ['source', 'expected']:
        need(audit[key]['sha256'] == plan['combined_audit'][key]['sha256'], 'Audit frame changed')
    source_text = blobs.get(audit['source']).decode()
    expected = blobs.json(audit['expected'])
    names = expected['names']
    need(len(names) == len(set(names)) == expected['count'] == 2275, 'Audit frame incomplete')
    need(parser.lean_imports(source_text) == plan['build_order'] and
         re.findall(r'^#print axioms (\S+)$', source_text, re.M) == names, 'Audit source differs')
    meta = evidence['audit_metadata']
    need(meta['status'] == 'passed' and meta['exit_code'] == 0 and
         meta['command'] == ['lake', 'env', 'lean', '--memory=2048', audit['source']['path']], 'Audit command differs')
    parsed = parser.parse_audits(blobs.get(audit['log']).decode())
    accepted = evidence['audit_acceptance']
    need(list(parsed) == names and parsed == expected['expected_axioms'] == accepted['axioms'], 'Audit names/axioms differ')
    need(accepted['count'] == 2275 and accepted['status'] == 'exact_actual_audit_passed' and
         accepted['log_sha256'] == audit['log']['sha256'], 'Accepted audit log differs')
    need(record['numeric_representatives_accepted_by_this_record'] is False and
         record['full815_constant_accepted'] is False and record['geometric_CohFT_accepted'] is False,
         'Invented numerical/geometric acceptance')
    for digest in record['blobs']:
        blobs.get({'sha256': digest})
    return {'status': 'verified_portably_without_Lean', 'targets': 17, 'transfers': 414,
            'audits': 2275, 'source_closure': 301, 'warning_logs': 34,
            'warning_blocks_per_log': 51, 'different_warning_order_logs': order_changes,
            'actual_build_seconds': round(elapsed, 3), 'decoded_evidence_bytes': blobs.total}


if __name__ == '__main__':
    arg = argparse.ArgumentParser(description=__doc__)
    arg.add_argument('--repository', type=Path, default=ROOT)
    arg.add_argument('--record', type=Path)
    args = arg.parse_args()
    u = utilities(args.repository)
    path = args.record or args.repository / 'environments/genus-two-f1-structural-transfers-validation.json'
    print(json.dumps(check(u.loads(path.read_bytes()), args.repository), indent=2))
