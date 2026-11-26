#!/usr/bin/env python3
"""Exercise fixed-fan curve/edge export, kernel replay, and claim binding."""

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'environments/gkm-inputs-osx-arm64.json'


def run(arguments):
    return subprocess.run(arguments, cwd=ROOT, text=True, capture_output=True)


def digest_targets(bundle):
    bundle['targets_sha256'] = hashlib.sha256(json.dumps(
        bundle['targets'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def change(bundle, path, value):
    part = bundle
    for component in path[:-1]:
        part = part[component]
    part[path[-1]] = value


def main():
    bundle = json.loads(INPUT.read_text())
    cases = []
    with tempfile.TemporaryDirectory(prefix='gw-gkm-curve-certificate-') as temporary:
        temporary = Path(temporary)

        def export(candidate, label, expected=True):
            source = temporary / (label + '.json')
            proof = temporary / (label + '.lean')
            digest_targets(candidate)
            source.write_text(json.dumps(candidate, sort_keys=True))
            started = time.perf_counter()
            result = run([sys.executable, 'scripts/export_gkm_curve_certificate.py',
                          str(source), '--output', str(proof)])
            seconds = time.perf_counter() - started
            if (result.returncode == 0) != expected:
                raise ValueError(f'{label}: unexpected export result\n{result.stderr}')
            if not expected:
                if 'GKM curve certificate export FAILED:' not in result.stderr:
                    raise ValueError(f'{label}: rejection was not controlled')
                cases.append({'case': label, 'gate': 'export', 'result': 'rejected'})
                return None
            started = time.perf_counter()
            checked = run(['lake', 'env', 'lean', str(proof)])
            if checked.returncode != 0:
                raise ValueError(f'{label}: kernel replay failed\n{checked.stdout}\n{checked.stderr}')
            if checked.stdout.strip() or checked.stderr.strip():
                raise ValueError(f'{label}: unexpected replay diagnostics\n{checked.stdout}\n{checked.stderr}')
            cases.append({'case': label, 'gate': 'kernel', 'result': 'accepted',
                          'export_seconds': round(seconds, 3),
                          'proof_check_seconds': round(time.perf_counter() - started, 3),
                          'proof_bytes': proof.stat().st_size,
                          'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest()})
            return proof

        baseline = export(copy.deepcopy(bundle), 'baseline_all_three_surfaces')
        if baseline.read_bytes() != (ROOT / 'AxiomaticGW/GKM/Fixtures/CurveReplay.lean').read_bytes():
            raise ValueError('Frozen curve replay differs from the public exporter')
        reversed_edge = copy.deepcopy(bundle)
        edge = reversed_edge['targets'][2]['edges'][0]
        edge['source'], edge['target'] = edge['target'], edge['source']
        edge['weight'] = [-value for value in edge['weight']]
        normal = edge['normal_bundles'][0]
        normal[0], normal[1] = normal[1], normal[0]
        export(reversed_edge, 'reversed_edge_orientation')
        reordered = copy.deepcopy(bundle)
        for target in reordered['targets']:
            target['edges'].reverse()
        export(reordered, 'reordered_edge_presentations')
        exchanged = copy.deepcopy(bundle)
        for target in exchanged['targets']:
            for tangent in target['tangent_characters']:
                tangent.reverse()
        export(exchanged, 'exchanged_tangent_branch_order')

        mutations = [
            ('same_energy_different_exceptional_class', ['targets',2,'edges',2,'class'], [0,1,0]),
            ('changed_curve_matrix', ['targets',2,'curve_to_signed_lattice',1,0], -1),
            ('changed_energy', ['targets',1,'energy_weights',1], 1),
            ('changed_ray', ['targets',0,'rays',0,0], 2),
            ('changed_cone', ['targets',1,'points',0,0], 1),
            ('changed_tangent', ['targets',2,'tangent_characters',3,0], [1,0]),
            ('changed_normal_degree', ['targets',1,'edges',2,'normal_bundles',0,2], 0),
            ('changed_normal_branch', ['targets',1,'edges',0,'normal_bundles',0,0], 1),
            ('changed_wall', ['targets',0,'edges',0,'wall'], [1]),
            ('changed_oriented_weight', ['targets',0,'edges',0,'weight'], [0,-1]),
            ('changed_intersection', ['targets',2,'divisor_curve_intersections',1,3], [1,1]),
            ('out_of_range_endpoint', ['targets',2,'edges',0,'source'], 5),
            ('out_of_range_cone_label', ['targets',2,'points',0,0], 5),
        ]
        for label, path, value in mutations:
            invalid = copy.deepcopy(bundle)
            change(invalid, path, value)
            export(invalid, label, False)
        missing = copy.deepcopy(bundle)
        missing['targets'][2]['edges'].pop()
        export(missing, 'missing_edge', False)

        prefix = '''import AxiomaticGW.GKM.Fixtures.CurveReplay
open AxiomaticGW.GKM.CurveConventionCertificate AxiomaticGW.GKM
'''
        bindings = {
            'rebind_curve_matrix': ('CurveFrames.TwoBlowups.request',
                '{CurveReplay.TwoBlowups.tables with curveMatrix := 0}'),
            'rebind_energy': ('CurveFrames.TwoBlowups.request',
                '{CurveReplay.TwoBlowups.tables with weights := 0}'),
            'rebind_intersections': ('CurveFrames.TwoBlowups.request',
                '{CurveReplay.TwoBlowups.tables with intersections := 0}'),
            'rebind_fan_request': ('{CurveFrames.TwoBlowups.request with rays := 0}',
                'CurveReplay.TwoBlowups.tables'),
            'rebind_generator_walls': ('{CurveFrames.TwoBlowups.request with generatorWalls := 0}',
                'CurveReplay.TwoBlowups.tables'),
            'rebind_state_tangent_sum': ('{CurveFrames.TwoBlowups.request with state := '
                '{CurveFrames.TwoBlowups.request.state with tangentSum := 0}}',
                'CurveReplay.TwoBlowups.tables'),
        }
        for label, (request, tables) in bindings.items():
            proof = temporary / (label + '.lean')
            proof.write_text(prefix + f'example : Accepts ({request}) ({tables}) := by\n'
                             '  exact CurveReplay.TwoBlowups.accepted\n')
            checked = run(['lake', 'env', 'lean', str(proof)])
            if checked.returncode == 0 or 'Type mismatch' not in checked.stdout:
                raise ValueError(f'{label}: expected claim-binding type rejection\n{checked.stdout}')
            cases.append({'case': label, 'gate': 'kernel', 'result': 'rejected'})
    print(json.dumps({'status': 'passed', 'cases': cases, 'case_count': len(cases),
                      'input_sha256': hashlib.sha256(INPUT.read_bytes()).hexdigest(),
                      'scope': 'fixed fan and full curve/invariant-edge conventions for X0/X1/X2; '
                               'presentation changes, export and kernel binding rejection; no GW values'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, IndexError, OSError) as error:
        print(f'GKM curve certificate regressions FAILED: {error}', file=sys.stderr)
        raise SystemExit(1)
