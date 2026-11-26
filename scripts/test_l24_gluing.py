#!/usr/bin/env python3
"""Reproduction and held-source binding for the full L24 gluing exporter."""
from pathlib import Path
import unittest
from unittest.mock import patch

import export_l24_gluing as exporter

ROOT = Path(__file__).resolve().parents[1]


class L24GluingTests(unittest.TestCase):
    def test_complete_reproduction(self):
        source, counts = exporter.generate()
        self.assertEqual(source, (ROOT / 'AxiomaticGW/Tautological/L24Gluing.lean').read_text())
        self.assertEqual(counts, {'columns': 815, 'expressions': 424, 'flag_permutations': 30})

    def test_every_held_source_is_bound(self):
        for name in exporter.SOURCE_PINS:
            with self.subTest(name=name), patch.dict(exporter.SOURCE_PINS, {name: '0' * 64}):
                with self.assertRaisesRegex(ValueError, 'Changed held source'):
                    exporter.generate()


if __name__ == '__main__':
    unittest.main(verbosity=2)
