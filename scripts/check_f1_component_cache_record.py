#!/usr/bin/env python3
"""Check portable evidence for the F1 component cache; do not run Lean.

This verifies source hashes, import closure and preserved offline audit excerpts.
It does not promote observed command results into a new kernel or repository
build result. The original Lean fixtures remain the mathematical certificates.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re

from check_gkm_inputs import integer, require, unique_object

PREFIX = 'AxiomaticGW.BlowupF1CompleteHComponents.'
ENTRY = 'AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsReplay'
HOT = {315, 331, 337, 341, 349, 354, 364, 369, 380, 669, 670, 672, 674, 675}
STANDARD = {'Classical.choice', 'Quot.sound', 'propext'}
AUDIT = re.compile(r"'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]", re.S)
COUNTS = {'components': 722, 'unique_cache_audit_declarations': 2170,
          'accepted_offline_runs': 125, 'supporting_trr_runs': 14, 'historical_failed_runs': 54,
          'project_sources': 495, 'introduced_fixture_sources': 268, 'preexisting_sources': 227,
          'direct_mathlib_sources': 60, 'reused_prior_component_values': 48,
          'full_frame_terms': 815, 'selected_nonzero_terms': 721}


def fields(value, expected, label):
    require(isinstance(value, dict) and set(value) == set(expected), 'Wrong fields: ' + label)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def hash_value(value):
    require(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value), 'Invalid SHA256')


def relative(value):
    require(isinstance(value, str) and value and not Path(value).is_absolute()
            and '..' not in Path(value).parts and '\\' not in value, 'Invalid relative path')
    return Path(value)


def load(raw):
    return json.loads(raw, object_pairs_hook=unique_object)


def lean_imports(source):
    """Read the pinned files' import declarations, ignoring comments and strings."""
    code = []
    i, depth, string, line = 0, 0, False, False
    while i < len(source):
        c, pair = source[i], source[i:i + 2]
        if line:
            code.append('\n' if c == '\n' else ' ')
            if c == '\n': line = False
            i += 1
        elif string:
            if c == '\\' and i + 1 < len(source):
                code.extend([' ', ' ']); i += 2
            else:
                if c == '"': string = False
                code.append('\n' if c == '\n' else ' '); i += 1
        elif depth:
            if pair in ('/-', '-/'):
                depth += 1 if pair == '/-' else -1
                code.extend([' ', ' ']); i += 2
            else:
                code.append('\n' if c == '\n' else ' '); i += 1
        elif pair in ('/-', '--'):
            depth, line = (1, False) if pair == '/-' else (0, True)
            code.extend([' ', ' ']); i += 2
        elif c == '"':
            string = True; code.append(' '); i += 1
        else:
            code.append(c); i += 1
    require(depth == 0 and not string, 'Unterminated Lean comment/string')
    imports = []
    for line in ''.join(code).splitlines():
        match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*', line)
        if match:
            names = match.group(1).split()
            require(all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name) for name in names),
                    'Unsupported Lean import syntax')
            imports.extend(names)
    require(len(set(imports)) == len(imports), 'Duplicate direct Lean import')
    return imports


def source_pin(root, row):
    hash_value(row['sha256'])
    path = root / relative(row['path'])
    require(path.is_file(), 'Missing source: ' + row['path'])
    raw = path.read_bytes()
    require(digest(raw) == row['sha256'],
            'Source hash mismatch: ' + row['path'])
    return raw


def payload(parent, pin):
    fields(pin, ['path', 'sha256', 'uncompressed_sha256', 'uncompressed_bytes'], 'sidecar pin')
    path = parent / relative(pin['path'])
    packed = path.read_bytes()
    hash_value(pin['sha256']); hash_value(pin['uncompressed_sha256'])
    require(digest(packed) == pin['sha256'], 'Compressed sidecar hash mismatch')
    raw = gzip.decompress(packed)
    require(len(raw) == integer(pin['uncompressed_bytes']) and
            digest(raw) == pin['uncompressed_sha256'], 'Uncompressed sidecar mismatch')
    return load(raw)


def transcript(raw):
    require(isinstance(raw, str), 'Expected audit transcript')
    result = {}
    for match in AUDIT.finditer(raw):
        name = match.group(1)
        axioms = [x.strip() for x in match.group(2).split(',') if x.strip()]
        require(name not in result, 'Duplicate audited declaration in transcript')
        require(len(set(axioms)) == len(axioms) and set(axioms) <= STANDARD, 'Nonstandard axiom')
        result[name] = set(axioms)
    require(result and not AUDIT.sub('', raw).strip(), 'Malformed or extra audit output')
    return result


def original_evidence(value):
    require(isinstance(value, dict) and value, 'Missing historical evidence')
    for pin in value.values():
        fields(pin, ['original_basename', 'sha256'], 'historical digest')
        name = relative(pin['original_basename'])
        require(len(name.parts) == 1, 'Historical evidence basename required')
        hash_value(pin['sha256'])


def passed_commands(rows):
    require(isinstance(rows, list) and rows, 'Missing offline commands')
    for row in rows:
        fields(row, ['command', 'exit_code', 'elapsed_seconds'], 'offline command')
        command = row['command']
        require(isinstance(command, list) and command and all(isinstance(x, str) for x in command),
                'Invalid command tokens')
        require(Path(command[0]).name == 'lean' and '--memory=2048' in command,
                'Changed kernel command or memory cap')
        require(integer(row['exit_code']) == 0, 'Failed offline command')
        require(type(row['elapsed_seconds']) in (int, float) and row['elapsed_seconds'] >= 0,
                'Invalid elapsed time')


def validate(record, closure, evidence, root):
    fields(record, ['schema_version', 'kind', 'date', 'status', 'scope', 'query', 'counts',
                    'acceptance', 'repository_integration', 'cache_symbol', 'entry_module',
                    'key_encoding', 'source_closure', 'offline_evidence', 'original_record_sha256',
                    'mathematical_effect', 'documentation_limitations', 'remaining'], 'record')
    require(integer(record['schema_version']) == 1 and record['kind'] == 'axiomatic_gw.f1_component_cache_validation',
            'Wrong validation schema')
    require(record['status'] == 'offline_component_cache_accepted_repository_build_pending', 'Changed acceptance scope')
    fields(record['counts'], COUNTS, 'counts')
    require({k: integer(v) for k, v in record['counts'].items()} == COUNTS, 'Wrong scope counts')
    accepted = {'component_cache': True, 'full_815_contraction': False, 'selected_721_contraction': False,
                'geometric_realization': False, 'actual_repository_build': False}
    require(record['acceptance'] == accepted and all(type(v) is bool for v in record['acceptance'].values()),
            'Unsupported mathematical or repository acceptance')
    require(record['entry_module'] == ENTRY and record['cache_symbol'] == PREFIX + 'cache', 'Wrong cache identity')
    require(record['query'] == {'target': 'F1', 'source_curve': [1, 1], 'added_points': 1,
                               'labels': ['hyperplane', 'exceptional:0', 'exceptional:0', 'exceptional:0']}, 'Changed query')
    require(all(type(x) is int for x in record['query']['source_curve']) and
            type(record['query']['added_points']) is int, 'Invalid query integers')
    require(record['key_encoding'] == {'layout': 'genus,curve_E,curve_F,then_label_psi_pairs',
                                       'labels': {'unit': 0, 'hyperplane': 1, 'exceptional:0': 2, 'point': 3}}, 'Changed full-key encoding')
    require(all(type(x) is int for x in record['key_encoding']['labels'].values()), 'Invalid label codes')
    integration = record['repository_integration']
    fields(integration, ['status', 'copied_sources', 'copied_source_bytes', 'compiled_artifacts_copied'], 'integration')
    require(integration['status'] == 'sources_preserved_actual_repository_build_pending' and
            integer(integration['copied_sources']) == 268 and integration['compiled_artifacts_copied'] is False,
            'Unexpected repository artifact claim')
    fields(record['original_record_sha256'], ['cache_acceptance', 'integration_manifest',
                                            'source_copy_record', 'candidate_input'], 'original records')
    for value in record['original_record_sha256'].values(): hash_value(value)

    fields(closure, ['schema_version', 'kind', 'entry_module', 'project_sources', 'direct_external_sources',
                     'environment', 'artifact_scope'], 'source closure')
    require(integer(closure['schema_version']) == 1 and closure['kind'] == 'axiomatic_gw.f1_component_cache_sources'
            and closure['entry_module'] == ENTRY, 'Wrong closure schema')
    project, external = {}, {}
    for row in closure['project_sources']:
        fields(row, ['module', 'path', 'sha256', 'offline_olean_sha256', 'introduced_fixture', 'imports'], 'project source')
        name = row['module']
        require(isinstance(name, str) and name.startswith('AxiomaticGW.') and name not in project, 'Repeated or invalid module')
        require(row['path'] == name.replace('.', '/') + '.lean', 'Source/module mismatch')
        raw_source = source_pin(root, row); hash_value(row['offline_olean_sha256'])
        require(type(row['introduced_fixture']) is bool and isinstance(row['imports'], list)
                and all(isinstance(x, str) for x in row['imports']) and len(set(row['imports'])) == len(row['imports']),
                'Invalid source classification/imports')
        require(set(lean_imports(raw_source.decode())) == set(row['imports']),
                'Source imports differ from recorded dependencies: ' + name)
        project[name] = row
    require(len(project) == 495 and sum(r['introduced_fixture'] for r in project.values()) == 268, 'Incomplete project closure')
    require(sum((root / r['path']).stat().st_size for r in project.values() if r['introduced_fixture']) ==
            integer(integration['copied_source_bytes']), 'Changed source byte count')
    for row in closure['direct_external_sources']:
        fields(row, ['module', 'path', 'sha256', 'offline_olean_sha256'], 'external source')
        name = row['module']
        require(isinstance(name, str) and name.startswith('Mathlib.') and name not in external, 'Invalid external module')
        require(row['path'] == '.lake/packages/mathlib/' + name.replace('.', '/') + '.lean', 'External path mismatch')
        source_pin(root, row); hash_value(row['offline_olean_sha256']); external[name] = row
    require(len(external) == 60, 'Incomplete direct external sources')
    require(len(closure['environment']) == 2 and {x['path'] for x in closure['environment']} ==
            {'lean-toolchain', 'lake-manifest.json'}, 'Incomplete environment pins')
    for row in closure['environment']:
        fields(row, ['path', 'sha256'], 'environment pin'); source_pin(root, row)
    state = {}
    def visit(name):
        require(state.get(name) != 1, 'Import cycle')
        if state.get(name) == 2: return
        require(name in project, 'Missing project dependency')
        state[name] = 1
        for dependency in project[name]['imports']:
            if dependency.startswith('Mathlib.'):
                require(dependency in external, 'Missing external dependency')
            else:
                visit(dependency)
        state[name] = 2
    visit(ENTRY)
    require(set(state) == set(project), 'Unreachable module in source closure')
    reused = 'AxiomaticGW.Surfaces.Fixtures.BlowupF1H121Components'
    require({n for n in project if n.startswith(reused)} ==
            {reused + 'Data'} | {reused + f'Value{i:02d}' for i in range(48)}, 'Incomplete prior48 proof reuse')

    fields(evidence, ['schema_version', 'kind', 'standard_axiom_allowlist', 'runs', 'supporting_trr_runs',
                      'audit_transcripts', 'historical_failed_runs', 'boundary'], 'offline evidence')
    require(integer(evidence['schema_version']) == 1 and evidence['kind'] == 'axiomatic_gw.f1_component_cache_offline_audits', 'Wrong audit schema')
    require(sorted(evidence['standard_axiom_allowlist']) == sorted(STANDARD), 'Changed axiom allowlist')
    transcripts = {}
    for key, body in evidence['audit_transcripts'].items():
        require(digest(body.encode()) == key, 'Changed audit transcript')
        transcripts[key] = transcript(body)
    all_audits, referenced = {}, set()
    require(len(evidence['runs']) == 125, 'Incomplete offline runs')
    for index, run in enumerate(evidence['runs']):
        fields(run, ['index', 'status', 'exit_code', 'elapsed_seconds', 'commands', 'modules',
                     'audited_declarations', 'audit_transcript', 'original_evidence'], 'offline run')
        require(integer(run['index']) == index and run['status'] == 'passed' and integer(run['exit_code']) == 0, 'Failed/repeated offline run')
        passed_commands(run['commands']); original_evidence(run['original_evidence'])
        require(run['modules'] and len(set(run['modules'])) == len(run['modules']) and
                all(name in project for name in run['modules']), 'Unbound run module')
        key = run['audit_transcript']; require(key in transcripts, 'Missing audit transcript'); referenced.add(key)
        require(run['audited_declarations'] == sorted(transcripts[key]), 'Run audit names differ from excerpt')
        for name, axioms in transcripts[key].items():
            require(name not in all_audits or all_audits[name] == axioms, 'Inconsistent repeated audit')
            all_audits[name] = axioms
    expected = {PREFIX + pattern.format(i) for i in range(722)
                for pattern in ('component_{}_computed', 'entry_{}_eq', 'key_index_{}')}
    expected |= {PREFIX + n for n in ['key_index', 'keys_injective', 'entries_eq', 'cache']}
    require(set(all_audits) == expected, 'Incomplete exact cache audit declarations')
    hot = set()
    for run in evidence['supporting_trr_runs']:
        fields(run, ['component_index', 'retained_trr_terms', 'status', 'exit_code', 'elapsed_seconds',
                     'commands', 'audit_transcript', 'original_evidence'], 'supporting TRR run')
        index = integer(run['component_index'])
        require(index in HOT and index not in hot, 'Unexpected/repeated repaired component'); hot.add(index)
        require(integer(run['retained_trr_terms']) == (31 if index < 600 else 32), 'Changed TRR term coverage')
        require(run['status'] == 'passed' and integer(run['exit_code']) == 0, 'Unaccepted TRR replay')
        passed_commands(run['commands']); original_evidence(run['original_evidence'])
        key = run['audit_transcript']; require(key in transcripts, 'Missing TRR transcript'); referenced.add(key)
        require(PREFIX + f'component_{index}_computed' in transcripts[key], 'Unbound original component equation')
        trr = f'AxiomaticGW.Component{index}TRR.'
        if index == 315:
            required = {trr + f'part_{i}_eq_zero' for i in range(31)}
            required |= {trr + name for name in ['terms_length', 'all_parts_zero', 'step_eq_zero']}
        else:
            required = {trr + f'part_{i}_checked' for i in range(31 if index < 600 else 32)}
            required |= {trr + name for name in ['terms_length', 'all_parts_checked', 'values_eq_claimed', 'step_computed']}
        required.add(PREFIX + f'component_{index}_computed')
        require(set(transcripts[key]) == required, 'Incomplete exact TRR part audits')
    require(hot == HOT and referenced == set(transcripts), 'Incomplete or unused supporting evidence')
    require(len(evidence['historical_failed_runs']) == 54, 'Historical failures omitted')
    for failure in evidence['historical_failed_runs']:
        fields(failure, ['status', 'exit_code', 'elapsed_seconds', 'original_evidence'], 'failed run')
        require(failure['status'] == 'failed' and integer(failure['exit_code']) != 0, 'Failure promoted to pass')
        original_evidence(failure['original_evidence'])
    return {'status': 'portable_offline_evidence_consistent', 'components': 722, 'cache_audits': len(all_audits),
            'offline_runs': 125, 'project_sources': len(project), 'actual_repository_build': False,
            'full_contraction_accepted': False}


def check(path, root):
    record = load(path.read_bytes())
    return validate(record, payload(path.parent, record['source_closure']),
                    payload(path.parent, record['offline_evidence']), root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--record', type=Path)
    args = parser.parse_args()
    path = args.record or args.root / 'environments/genus-two-f1-h-component-cache-validation.json'
    print(json.dumps(check(path, args.root), sort_keys=True))


if __name__ == '__main__':
    main()
