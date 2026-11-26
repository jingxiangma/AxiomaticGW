#!/usr/bin/env python3
"""Reproduction and malformed-input tests for complete L24 column replay."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import export_surface_l24_fixture as exporter

ROOT = Path(__file__).resolve().parents[1]
PAYLOAD = (ROOT / 'environments/surface-l24-plane-zero-columns.json').read_bytes()


class SurfaceL24FixtureTests(unittest.TestCase):
    def test_complete_reproduction(self):
        self.assertEqual(exporter.generate(PAYLOAD),
                         (ROOT / 'AxiomaticGW/Surfaces/Fixtures/L24.lean').read_text())

    def test_every_held_source_is_bound(self):
        for name in exporter.SOURCE_PINS:
            with self.subTest(name=name), patch.dict(exporter.SOURCE_PINS, {name: '0' * 64}):
                with self.assertRaises(ValueError):
                    exporter.generate(PAYLOAD)

    def test_complete_unique_column_indices(self):
        rows = json.loads(PAYLOAD)
        incomplete = rows[:-1]
        duplicate = copy.deepcopy(rows)
        duplicate[42]['column'] = 41
        for data in (incomplete, duplicate):
            with self.assertRaises(ValueError):
                exporter.generate(json.dumps(data))

    def test_exact_numbers_and_residual_requests(self):
        for mutation in ('zero_denominator', 'boolean_coefficient', 'fractional_power',
                         'negative_power', 'wrong_genus', 'wrong_curve', 'unknown_state'):
            rows = json.loads(PAYLOAD)
            term = next(row['terms'][0] for row in rows if row['terms'])
            query = term['monomial'][0]
            if mutation == 'zero_denominator':
                term['coefficient'][1] = 0
            elif mutation == 'boolean_coefficient':
                term['coefficient'][0] = True
            elif mutation == 'fractional_power':
                query['insertions'][0][1] = 0.5
            elif mutation == 'negative_power':
                query['insertions'][0][1] = -1
            elif mutation == 'wrong_genus':
                query['genus'] = 1
            elif mutation == 'wrong_curve':
                query['curve'] = [1]
            else:
                query['insertions'][0][0] = 3
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                exporter.generate(json.dumps(rows))

    def test_duplicate_json_keys(self):
        with self.assertRaises(ValueError):
            exporter.generate('[{"column":0,"column":1,"terms":[]}]')


if __name__ == '__main__':
    unittest.main(verbosity=2)
