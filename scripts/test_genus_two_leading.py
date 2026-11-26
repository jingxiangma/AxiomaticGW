#!/usr/bin/env python3
"""Test request binding of the finite leading-matrix diagnostic in pinned Sage."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from compare_genus_two_leading import explore
from export_genus_two_leading import generate

ROOT = Path(__file__).resolve().parents[1]


class LeadingMatrixTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = (ROOT / "environments/genus-two-leading-matrix-native.json").read_bytes()
        cls.data = json.loads(cls.payload)

    def test_held_equations_and_search_rows(self):
        report = explore(self.payload)
        expected = json.loads((ROOT / "environments/genus-two-leading-matrix-exploration.json").read_bytes())
        self.assertEqual(json.loads(json.dumps(report)), expected)
        self.assertEqual(sum(r["matches_held_full_normalization"] is True
                             for r in report["equations"]), 19)
        self.assertEqual(len(report["equations"]), 25)

    def test_exact_generated_program(self):
        self.assertEqual(generate(), (ROOT / "scripts/GenusTwoLeading.lean").read_text())

    def test_corrupted_requests_and_coefficients(self):
        for kind in ("coefficient", "curve", "equal_energy_curve", "missing_column",
                     "duplicate_case", "missing_case", "zero_denominator", "labels"):
            with self.subTest(kind=kind):
                changed = copy.deepcopy(self.data)
                first = changed["cases"][0]
                if kind == "coefficient":
                    first["coefficients"][0] = [1, 1]
                elif kind == "curve":
                    first["curve"] = [1]
                elif kind == "equal_energy_curve":
                    row = next(c for c in changed["cases"] if c["name"] == "bl2_E1_E1E1E1")
                    row["columns"][0]["curve"] = [0, 1, 0]
                elif kind == "missing_column":
                    first["columns"].pop(0)
                    first["coefficients"].pop(0)
                elif kind == "duplicate_case":
                    changed["cases"].append(copy.deepcopy(first))
                elif kind == "missing_case":
                    changed["cases"].pop(0)
                elif kind == "zero_denominator":
                    first["coefficients"][0][1] = 0
                else:
                    first["labels"][0] = 2
                with self.assertRaises(ValueError):
                    explore(json.dumps(changed).encode())


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="genus-two-leading-test-") as cache:
        for variable, name in (("DOT_SAGE", "sage"), ("MPLCONFIGDIR", "matplotlib"),
                               ("XDG_CACHE_HOME", "xdg")):
            path = Path(cache) / name
            path.mkdir()
            os.environ[variable] = str(path)
        unittest.main()
