"""Verify the saved node/zero validation records using only repository files.

Historical commands, logs and artifact paths are embedded provenance, not paths
to execute or open. This checks recorded evidence; it does not run Lean or
establish new geometric or numerical claims.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import types

ROOT = Path(__file__).resolve().parents[1]
HELPER = 'scripts/check_f1_root_zero_record.py'
HELPER_SHA = 'fdc46be68d7f1b8b5a523bf01a2f3d47970803c60502a8065f2924f41ba755bb'
CONFIG = {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}
RECORDS = ['environments/gkm-hodge-node-normal-validation.json',
           'environments/genus-two-f1-root-zero-rows-validation.json']
NODE_ROOTS = ['AxiomaticGW.Tautological.NonseparatingNodeNormal',
              'AxiomaticGW.GKM.Fixtures.HodgeNodeNormal',
              'AxiomaticGWTest.GKM.HodgeNodeNormal']
ZERO_ROOTS = ['AxiomaticGW.Surfaces.Fixtures.BlowupF1RootZeroRows.' + name for name in
              ['CoefficientBatch00', 'CoefficientBatch01', 'CoefficientBatch02',
               'CoefficientBatch03', 'GuardBatch00', 'GuardBatch01']] + [
                   'AxiomaticGW.Surfaces.ScalarPointRootZero',
                   'AxiomaticGW.Surfaces.Fixtures.BlowupF1Root123DimensionZero']


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'Duplicate JSON field')
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def repository_path(repository, value):
    need(isinstance(value, str) and value and '\\' not in value, 'Invalid relative path')
    path = Path(value)
    need(not path.is_absolute() and '..' not in path.parts and str(path) == value,
         'Noncanonical relative path')
    result = repository / path
    need(result.resolve().is_relative_to(repository.resolve()), 'Repository path escapes root')
    return result


def load_helper(repository):
    path = repository_path(repository, HELPER)
    raw = path.read_bytes()
    need(digest(raw) == HELPER_SHA, 'Parser/lexer changed before execution')
    helper = types.ModuleType('checked_root_record_helper')
    helper.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), helper.__dict__)
    return helper


def warnings(text):
    blocks = re.findall(r'(?ms)^warning: .*?^Note: This linter can be disabled with `[^\n]+`', text)
    need(len(blocks) == len(re.findall(r'(?m)^warning: ', text)), 'Unclassified warning format')
    return blocks


def check_record(record, repository=ROOT, helper=None):
    """Verify embedded evidence and the canonical current source/configuration closure."""
    repository = Path(repository)
    helper = helper or load_helper(repository)
    need(type(record['schema_version']) is int and record['schema_version'] == 1, 'Unsupported record schema')
    need(record['status'] == 'actual_targeted_builds_and_public_axioms_passed', 'Wrong status')
    kind = record['kind']
    need(kind in {'node_normal', 'zero_rows'}, 'Unknown scope kind')
    configs = [row['path'] for row in record['configuration']]
    need(len(configs) == 3 and set(configs) == CONFIG, 'Exact three canonical config paths required')
    support = [HELPER] + ([] if kind == 'node_normal' else [
        'scripts/export_f1_root_zero_rows.py', 'scripts/test_f1_root_zero_rows.py',
        'scripts/export_f1_root_relabel_transfers.py'])
    need([row['path'] for row in record['supporting_repository_sources']] == support,
         'Supporting source frame changed')
    for row in record['configuration'] + record['supporting_repository_sources']:
        need(digest(repository_path(repository, row['path']).read_bytes()) == row['sha256'],
             'Repository pin changed')
    frame = record['source_closure']
    bymodule = {row['module']: row for row in frame['modules']}
    need(len(bymodule) == len(frame['modules']) == frame['module_count'] ==
         (53 if kind == 'node_normal' else 291), 'Closure count')
    need(frame['roots'] == (NODE_ROOTS if kind == 'node_normal' else ZERO_ROOTS), 'Root scope changed')
    order = [row['module'] for row in frame['modules']]
    need(frame['import_order'] == order, 'Recorded import order differs')
    seen, external = set(), set()
    for row in frame['modules']:
        module = row['module']
        need(re.fullmatch(r'(?:AxiomaticGW|AxiomaticGWTest)(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module),
             'Invalid project module')
        canonical = module.replace('.', '/') + '.lean'
        need(row['path'] == canonical, 'Module path is not canonical')
        raw = repository_path(repository, canonical).read_bytes()
        need(digest(raw) == row['sha256'], 'Closure source drift')
        actual = helper.lean_imports(raw.decode())
        need(actual == row['imports'], 'Exact lexical imports changed')
        for name in actual:
            if name.startswith(('AxiomaticGW.', 'AxiomaticGWTest.')):
                need(name in seen, 'Closure is not dependency ordered')
            else:
                external.add(name)
        seen.add(module)
    need(frame['external_imports'] == sorted(external), 'External import union differs')
    reachable = set()

    def visit(module):
        need(module in bymodule, 'Missing dependency')
        if module in reachable:
            return
        reachable.add(module)
        for name in bymodule[module]['imports']:
            if name.startswith(('AxiomaticGW.', 'AxiomaticGWTest.')):
                visit(name)

    for root in frame['roots']:
        visit(root)
    need(reachable == set(bymodule), 'Extraneous closure node')
    need([row['module'] for row in record['builds']] == frame['roots'], 'Build scope changed')
    prior = record['warning_reference']['full_log']
    need(digest(prior['text'].encode()) == prior['sha256'], 'Prior log changed')
    prior_warnings = warnings(prior['text'])
    need(len(prior_warnings) == 52, 'Prior warning frame changed')
    for run in record['builds']:
        meta, log = run['metadata'], run['full_log']
        need(digest(log['text'].encode()) == log['sha256'] == meta['log']['sha256'], 'Build log changed')
        need(meta['status'] == 'passed' and meta['exit_code'] == 0, 'Build failed')
        need(meta['command'] == [record['lake_executable'], '--no-ansi', '--no-cache', 'build', run['module']],
             'Unexpected build command')
        need(meta['timeout_seconds'] == 120 and meta['rss_limit_bytes'] == 2147483648, 'Resource limit changed')
        need(meta['max_sampled_concurrent_lean_children'] == 1 and
             0 < meta['peak_sampled_lean_rss_bytes'] <= meta['rss_limit_bytes'] and
             not meta['violations'], 'Resource observation failed')
        need('Build completed successfully' in log['text'] and
             not re.search(r'\berror:|sorryAx|memory_exception', log['text']), 'Bad build output')
        blocks = warnings(log['text'])
        need(blocks == run['inherited_warning_blocks'], 'Stored warnings changed')
        need(all(block in prior_warnings for block in blocks), 'New warning')
        count = 51 if run['module'].startswith('AxiomaticGW.Surfaces.Fixtures.BlowupF1Root') else 0
        need(len(blocks) == count, 'Unexpected inherited warning count')
        need(run['source']['sha256'] == bymodule[run['module']]['sha256'], 'Built source differs')
    audit = record['actual_combined_audit']
    need(audit['metadata']['status'] == 'passed' and audit['metadata']['exit_code'] == 0, 'Audit failed')
    need(audit['metadata']['command'] == ['lake', 'env', 'lean', '--memory=2048', audit['source']['path']],
         'Unexpected audit command')
    for row in [audit['source'], audit['full_log']]:
        need(digest(row['text'].encode()) == row['sha256'], 'Audit evidence changed')
    names = audit['expected_names']
    need(len(names) == len(set(names)) == 288, 'Combined audit frame changed')
    need(re.findall(r'^#print axioms (\S+)$', audit['source']['text'], re.M) == names,
         'Audit source names differ')
    expected_imports = NODE_ROOTS + ZERO_ROOTS
    need([step['module'] for step in record['combined_build_ledger']['record']['steps']] == expected_imports,
         'Combined build scope changed')
    need(helper.lean_imports(audit['source']['text']) == expected_imports, 'Combined audit imports differ')
    parsed = helper.parse_audits(audit['full_log']['text'])
    need(list(parsed) == names, 'Audit output names differ')
    own = record['audit_names']
    need(own == [name for name in names if name in own] and len(set(own)) == record['audit_count'],
         'Own audit scope')
    need(record['audit_results'] == {name: parsed[name] for name in own}, 'Own audit results differ')
    if kind == 'node_normal':
        need(own == names[:17] and len(own) == 17, 'Node scope changed')
    else:
        need(own == names[17:] and len(own) == 271, 'Zero scope changed')
        groups = record['original_index_partition']['groups']
        need(list(groups) == ['accepted_representatives', 'remaining_representatives',
                             'structural_transfer_targets', 'coefficient_zero',
                             'nonzero_coefficient_genus_guard'], 'Index group names changed')
        need([len(group) for group in groups.values()] == [3, 277, 414, 94, 27], 'Index counts changed')
        need(sorted(i for group in groups.values() for i in group) == list(range(815)), 'Index partition changed')
        need(sorted(groups['coefficient_zero'] + groups['nonzero_coefficient_genus_guard']) == list(range(121)),
             'Zero prefix changed')
        py = record['installed_python_validation']
        need(py['metadata']['status'] == 'passed' and py['metadata']['exit_code'] == 0, 'Python failed')
        need(digest(py['full_log']['text'].encode()) == py['full_log']['sha256'], 'Python log changed')
        need(re.search(r'Ran 12 tests in [0-9.]+s\n\nOK\n', py['full_log']['text']) is not None,
             'Python suite incomplete')
        need(record['accepted_original_weighted_zero_indices'] == list(range(121)), 'Weighted zero scope changed')
        need(record['whole_row_123_or_124_accepted'] is False, 'Invented complete row value')
    need(record['full815_constant_accepted'] is False and record['geometric_CohFT_accepted'] is False,
         'Invented completion boundary')
    return {'kind': kind, 'source_count': frame['module_count'], 'audit_count': len(own),
            'status': 'record_verified_without_Lean_or_temporary_inputs'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', type=Path, default=ROOT)
    parser.add_argument('--record', type=Path, action='append', help='Explicit record input; repeat for both.')
    args = parser.parse_args()
    repository = args.repository.resolve()
    helper = load_helper(repository)
    paths = args.record or [repository / name for name in RECORDS]
    for path in paths:
        print(json.dumps(check_record(load(path), repository, helper)))


if __name__ == '__main__':
    main()
