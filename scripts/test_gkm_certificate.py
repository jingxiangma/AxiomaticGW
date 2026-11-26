#!/usr/bin/env python3
"""Exercise standalone GKM state certificate export and Lean kernel replay."""

import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

import check_gkm_inputs as codec

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'environments/gkm-inputs-osx-arm64.json'


def run(arguments):
    return subprocess.run(arguments, cwd=ROOT, text=True, capture_output=True)


def digest_targets(bundle):
    bundle['targets_sha256'] = hashlib.sha256(json.dumps(
        bundle['targets'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def constant(value):
    return {'numerator': [] if not value else [[[0, 0], [value, 1]]],
            'denominator': [[[0, 0], [1, 1]]],
            'denominator_nonzero_term': [[0, 0], [1, 1]]}


def main():
    bundle = json.loads(INPUT.read_text())
    cases = []
    with tempfile.TemporaryDirectory(prefix='gw-gkm-certificate-') as temporary:
        temporary = Path(temporary)
        def export(candidate, label, expected=True, target=None):
            source = temporary / (label + '.json')
            proof = temporary / (label + '.lean')
            source.write_text(json.dumps(candidate, sort_keys=True))
            arguments = [sys.executable, 'scripts/export_gkm_certificate.py',
                         str(source), '--output', str(proof)]
            if target is not None:
                arguments += ['--target', target]
            started = time.perf_counter()
            result = run(arguments)
            export_seconds = time.perf_counter() - started
            if (result.returncode == 0) != expected:
                raise ValueError(f'{label}: unexpected export result\n{result.stderr}')
            if not expected:
                if 'GKM certificate export FAILED:' not in result.stderr:
                    raise ValueError(f'{label}: rejection was not controlled')
                cases.append({'case': label, 'gate': 'export', 'result': 'rejected'})
                return None
            started = time.perf_counter()
            checked = run(['lake', 'env', 'lean', str(proof)])
            proof_seconds = time.perf_counter() - started
            if checked.returncode != 0:
                raise ValueError(f'{label}: kernel replay failed\n{checked.stdout}\n{checked.stderr}')
            cases.append({'case': label, 'gate': 'kernel', 'result': 'accepted',
                          'targets': ['X0', 'X1', 'X2'] if target is None else [target],
                          'export_seconds': round(export_seconds, 3),
                          'proof_check_seconds': round(proof_seconds, 3),
                          'proof_bytes': proof.stat().st_size,
                          'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest()})
            return proof
        baseline = export(bundle, 'baseline_all_three_surfaces')
        frozen = ROOT / 'AxiomaticGW/GKM/Fixtures/SurfaceReplay.lean'
        if baseline.read_bytes() != frozen.read_bytes():
            raise ValueError('Frozen replay differs from the current public exporter')
        equivalent = copy.deepcopy(bundle)
        value = equivalent['targets'][0]['metric'][1][2]
        for part in ('numerator', 'denominator'):
            for _, coefficient in value[part]:
                coefficient[0] *= 7
        value['denominator_nonzero_term'][1][0] *= 7
        digest_targets(equivalent)
        export(equivalent, 'equivalent_symbolic_metric_representative', target='X0')
        vanishing_sample = copy.deepcopy(bundle)
        value = vanishing_sample['targets'][0]['metric'][1][2]
        multiplier = {(0, 0): Fraction(1), (0, 1): Fraction(-1), (1, 0): Fraction(1)}
        for part in ('numerator', 'denominator'):
            product = codec.multiply_polynomials(codec.polynomial(value[part]), multiplier)
            value[part] = [[list(powers), [q.numerator, q.denominator]]
                           for powers, q in sorted(product.items())]
        value['denominator_nonzero_term'] = copy.deepcopy(value['denominator'][0])
        digest_targets(vanishing_sample)
        export(vanishing_sample, 'regular_representative_vanishing_at_initial_sample', target='X0')
        for label, field in [('changed_metric', 'metric'), ('changed_inverse', 'fixedpoint_to_basis'),
                             ('changed_restrictions', 'basis_to_fixedpoint')]:
            invalid = copy.deepcopy(bundle)
            invalid['targets'][0][field][0][0] = constant(2)
            digest_targets(invalid)
            export(invalid, label, False)
        invalid = copy.deepcopy(bundle)
        invalid['targets'][0]['euler'][0] = constant(0)
        digest_targets(invalid)
        export(invalid, 'zero_euler', False)
        prefix = '''import AxiomaticGW.GKM.Fixtures.SurfaceReplay
open AxiomaticGW.GKM.StateSpaceCertificate AxiomaticGW.GKM
'''
        negative = {
            'rebind_zero_metric': ('SurfaceFrames.Plane.request',
                '{SurfaceReplay.Plane.tables with metric := 0}'),
            'rebind_zero_inverse': ('SurfaceFrames.Plane.request',
                '{SurfaceReplay.Plane.tables with inverse := 0}'),
            'rebind_zero_product': ('SurfaceFrames.Plane.request',
                '{SurfaceReplay.Plane.tables with products := 0}'),
            'rebind_c1': ('SurfaceFrames.Plane.request',
                '{SurfaceReplay.Plane.tables with c1 := 0}'),
            'rebind_unit_label': ('{SurfaceFrames.Plane.request with unitIndex := 1}',
                'SurfaceReplay.Plane.tables'),
            'rebind_ordinary_metric': ('{SurfaceFrames.Plane.request with ordinaryMetric := 0}',
                'SurfaceReplay.Plane.tables'),
            'rebind_ordinary_product': ('{SurfaceFrames.Plane.request with ordinaryProducts := 0}',
                'SurfaceReplay.Plane.tables'),
            'rebind_ordinary_c1': ('{SurfaceFrames.Plane.request with ordinaryC1 := 0}',
                'SurfaceReplay.Plane.tables'),
            'rebind_restriction_request': ('{SurfaceFrames.Plane.request with restrictions := 0}',
                'SurfaceReplay.Plane.tables'),
            'rebind_euler_request': ('{SurfaceFrames.Plane.request with euler := 0}',
                'SurfaceReplay.Plane.tables'),
            'rebind_tangent_request': ('{SurfaceFrames.Plane.request with tangentSum := 0}',
                'SurfaceReplay.Plane.tables'),
        }
        for label, (request, tables) in negative.items():
            proof = temporary / (label + '.lean')
            proof.write_text(prefix + f'example : Accepts ({request}) ({tables}) := by\n'
                             '  exact SurfaceReplay.Plane.accepted\n')
            checked = run(['lake', 'env', 'lean', str(proof)])
            if checked.returncode == 0 or 'Type mismatch' not in checked.stdout:
                raise ValueError(f'{label}: expected claim-binding type rejection\n{checked.stdout}')
            cases.append({'case': label, 'gate': 'kernel', 'result': 'rejected'})
    print(json.dumps({'status': 'passed', 'cases': cases, 'case_count': len(cases),
                      'input_sha256': hashlib.sha256(INPUT.read_bytes()).hexdigest(),
                      'scope': 'classical state tables for X0/X1/X2, equivalent representation, '
                               'export rejection and kernel claim-binding rejection; no GW values'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        print(f'GKM certificate regression FAILED: {error}', file=sys.stderr)
        raise SystemExit(1)
