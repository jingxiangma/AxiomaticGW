"""Verify two targeted records using the existing bounded-log and audit utilities."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import types

ROOT = Path(__file__).resolve().parents[1]
UTILITY = 'scripts/check_f1_actual_numeric_record.py'
UTILITY_SHA = 'fe8c4f9d8d67a8557d69e0e51aa3cb0da9515cc9aba762964d9d11e0d4203208'
FRAMES = {'loop_square_gluing': 'cdcc5fbb92e73335cb8eb457dcd7535aedd219b9d9c5a9fe8522779f22684fb6',
          'scalar_root_order': 'c29bf35a349a698312e9567857dd907aeb684f491777b6a3607dddbc7b1d8090'}
RECORDS = ['environments/gkm-loop-square-gluing-validation.json',
           'environments/scalar-point-root-order-validation.json']


def utilities(repository):
    path = repository / UTILITY
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != UTILITY_SHA:
        raise ValueError('Utilities changed before execution')
    module = types.ModuleType('verified_bounded_utilities'); module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def check(record, repository=ROOT):
    repository = Path(repository)
    u = utilities(repository); need = u.need; parser = u.load_helper(repository)
    need(type(record['schema_version']) is int and record['schema_version'] == 1, 'Wrong schema')
    kind = record['kind']
    need(kind in FRAMES and record['status'] == 'actual_targeted_validation_passed', 'Wrong record scope')
    need(record['frame']['sha256'] == FRAMES[kind], 'Frozen frame differs')
    blobs = u.Blobs(record['blobs']); frame = blobs.json(record['frame'])
    need(frame['kind'] == kind, 'Frame kind differs')
    config = frame['configuration']
    need(len(config) == 3 and {row['path'] for row in config} == u.CONFIG, 'Canonical config frame required')
    for row in config:
        need(u.sha(u.relative(repository, row['path']).read_bytes()) == row['sha256'], 'Config changed')
    closure = frame['source_closure']; bymodule = {}; external = set()
    need(len(closure['modules']) == closure['module_count'] == (69 if kind == 'loop_square_gluing' else 505),
         'Source closure count differs')
    for row in closure['modules']:
        need(row['path'] == row['module'].replace('.', '/') + '.lean', 'Noncanonical module path')
        raw = u.relative(repository, row['path']).read_bytes()
        need(u.sha(raw) == row['sha256'], 'Source pin changed')
        need(parser.lean_imports(raw.decode()) == row['imports'], 'Lexical imports changed')
        for name in row['imports']:
            if name.startswith(('AxiomaticGW.', 'AxiomaticGWTest.')):
                need(name in bymodule, 'Source closure not topological')
            else:
                external.add(name)
        need(row['module'] not in bymodule, 'Duplicate module')
        bymodule[row['module']] = row
    need(closure['import_order'] == list(bymodule) and closure['external_imports'] == sorted(external),
         'Recorded order or external union differs')
    need(len(closure['roots']) == 2 and set(closure['roots']) <= set(bymodule), 'Root scope differs')
    baseline = set()
    if kind == 'scalar_root_order':
        reference = frame['warning_reference']
        raw = u.relative(repository, reference['path']).read_bytes()
        need(u.sha(raw) == reference['sha256'], 'Frozen warning record changed')
        old = u.loads(raw); old_blobs = u.Blobs(old['blobs'])
        for run in old['runs']:
            for key in ['build_log', 'prerequisite_log']:
                baseline.update(u.warning_blocks(old_blobs.get(run[key]).decode()))
        need(len(baseline) == 1805, 'Frozen warning catalogue differs')
    build_seconds, warning_counts, build_modes = [], [], []
    for run in frame['runs']:
        meta = blobs.json(run['metadata']); text = blobs.get(run['log']).decode()
        need(meta['command'] == run['command'] and meta['status'] == 'passed' and meta['exit_code'] == 0,
             'Unsuccessful or different build command')
        need(not re.search(r'\berror:|sorryAx|memory_exception', text) and
             ('Build completed successfully' in text or 'All targets up-to-date' in text), 'Build diagnostic')
        warnings = u.warning_blocks(text)
        need(len(warnings) == run['expected_warning_count'] and set(warnings) <= baseline, 'Unreviewed warning')
        warning_counts.append(len(warnings))
        if run['mode'] == 'sampled':
            timeout = 30 if run['purpose'] == 'prerequisites' else 120
            children = 0 if run['purpose'] == 'prerequisites' else 1
            need(meta['timeout_seconds'] == timeout and meta['rss_limit_bytes'] == 3 * 1024**3
                 and meta['max_sampled_concurrent_lean_children'] == children and not meta['violations']
                 and 0 <= meta['peak_sampled_lean_rss_bytes'] <= 3 * 1024**3, 'Build sampled resources differ')
            if children:
                need(meta['peak_sampled_lean_rss_bytes'] > 0, 'No actual compiler observed')
            need(meta['log']['sha256'] == run['log']['sha256'], 'Sampled build log differs')
        else:
            need(run['mode'] == 'simple' and 'rss_limit_bytes' not in meta
                 and 'timeout_seconds' not in meta, 'Simple wrapper misrepresented as sampled')
        if run['purpose'] == 'build':
            need(meta['command'][-1] in closure['roots'], 'Unexpected built target')
            build_seconds.append(meta['elapsed_seconds']); build_modes.append(run['mode'])
    need(len(build_seconds) == frame['build_count'] == 2, 'Actual build count differs')
    audit = frame['audit']; metadata = blobs.json(audit['metadata'])
    source_text = blobs.get(frame['audit_source']).decode()
    need(metadata['status'] == 'passed' and metadata['exit_code'] == 0
         and metadata['command'] == audit['command'], 'Audit command failed or differs')
    heap = 2048 if kind == 'loop_square_gluing' else 3072
    need(Path(metadata['command'][0]).name == 'lake' and metadata['command'][1:] ==
         ['env', 'lean', '--memory=' + str(heap), frame['audit_source']['path']], 'Audit source/heap differs')
    expected = frame['expected_axioms']
    need(len(expected) == (16 if kind == 'loop_square_gluing' else 6), 'Audit count differs')
    need(parser.lean_imports(source_text) == [closure['roots'][-1]] and
         re.findall(r'^#print axioms (\S+)$', source_text, re.M) == list(expected), 'Audit source frame differs')
    parsed = parser.parse_audits(blobs.get(audit['log']).decode())
    need(list(parsed) == list(expected) and parsed == expected, 'Exact audit names/axioms differ')
    if kind == 'scalar_root_order':
        need(metadata['timeout_seconds'] == 120 and metadata['rss_limit_bytes'] == 3 * 1024**3 and
             metadata['max_sampled_concurrent_lean_children'] == 1 and not metadata['violations'] and
             0 < metadata['peak_sampled_lean_rss_bytes'] <= 3 * 1024**3 and
             metadata['log']['sha256'] == audit['log']['sha256'], 'Successful audit monitoring differs')
        failed = frame['failed_actual_audit']; failed_metadata = blobs.json(failed['metadata'])
        need(failed_metadata['status'] == 'failed' and failed_metadata['exit_code'] == 134 and
             failed_metadata['command'][3] == '--memory=2048' and
             'memory_exception' in blobs.get(failed['log']).decode(), 'Lost earlier audit memory failure')
    for reference in frame['history']:
        blobs.get(reference)
    for digest in record['blobs']:
        blobs.get({'sha256': digest})
    need(record['geometric_boundary_square_accepted'] is False and record['full815_constant_accepted'] is False,
         'Invented geometric/full-constant acceptance')
    return {'kind': kind, 'sources': len(bymodule), 'build_seconds': build_seconds,
            'build_monitoring': build_modes, 'warnings_per_build_or_preflight': warning_counts,
            'audit_names': len(parsed), 'audit_seconds': metadata['elapsed_seconds'],
            'audit_lean_memory_mib': heap, 'audit_monitoring': audit['mode'],
            'status': 'verified_portably_without_Lean_or_historical_path_reads'}


if __name__ == '__main__':
    arg = argparse.ArgumentParser(description=__doc__)
    arg.add_argument('--repository', type=Path, default=ROOT)
    arg.add_argument('--record', type=Path, action='append')
    args = arg.parse_args(); u = utilities(args.repository)
    for path in args.record or [args.repository / name for name in RECORDS]:
        print(json.dumps(check(u.loads(path.read_bytes()), args.repository)))
