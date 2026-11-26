#!/usr/bin/env python3
"""Offline reproduction and kernel-proved rejection cases for the BP initial replay."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import export_l24_initial as exporter

ROOT = Path(__file__).resolve().parents[1]


def rational(value):
    p, q = value
    return str(p) if q == 1 else f"({p} / {q})"


class L24InitialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = subprocess.run(["lake", "-q", "exe", "decoratedPullback"], cwd=ROOT,
                                capture_output=True, check=True, timeout=240)
        cls.raw = result.stdout
        cls.hints, cls.records = exporter.produce(cls.raw)

    def prove(self, text, name):
        with tempfile.TemporaryDirectory(prefix="gw-l24-initial-negative-") as tmp:
            path = Path(tmp) / (name + ".lean")
            path.write_text(
                "import AxiomaticGW.Tautological.Fixtures.L24InitialReplay\n"
                "open AxiomaticGW\nset_option maxRecDepth 20000\n" + text)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    text=True, capture_output=True, timeout=240)
            # The negation must compile; any error or timeout is a failed test.
            self.assertEqual(result.returncode, 0, name + "\n" + result.stdout + result.stderr)

    def test_reproducible_export(self):
        sources = exporter.replay_sources(self.raw)
        for name, source in sources.items():
            self.assertEqual(source, (ROOT / "AxiomaticGW/Tautological" / name).read_text())
        self.assertEqual(len(self.hints), 409)
        self.assertEqual([len(row) for row in self.records], [306] * 4)
        self.assertEqual([sum(q[0] == 0 for _, q in row) for row in self.records],
                         [18, 60, 60, 60])

    def test_source_and_payload_binding(self):
        duplicate = self.raw.replace(b'"schema_version":1',
                                     b'"schema_version":1,"schema_version":1', 1)
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            exporter.context(duplicate)
        for mutate in (lambda d: d["cases"].pop(),
                       lambda d: d["cases"][0]["terms"][0].update(coefficient=2),
                       lambda d: d.update(schema_version=True)):
            data = json.loads(self.raw)
            mutate(data)
            with self.assertRaisesRegex(ValueError, "Native payload differs"):
                exporter.context(json.dumps(data).encode())
        for name in exporter.SOURCE_PINS:
            with patch.dict(exporter.SOURCE_PINS, {name: "0" * 64}):
                with self.assertRaisesRegex(ValueError, "Changed held source"):
                    exporter.context(self.raw)

    def test_kernel_rejects_corrupted_records(self):
        row = self.records[0]
        zero = next(i for i, (_, q) in enumerate(row) if q[0] == 0)
        negative = next(i for i, (_, q) in enumerate(row) if q[0] < 0)
        positive = next(i for i, (_, q) in enumerate(row) if q[0] > 0)
        destination, q = row[negative]
        changes = {
            "lost_negative_term": f"L24InitialReplay.records0.eraseIdx {negative}",
            "false_pruning": f"L24InitialReplay.records0.set {positive} (0, 0)",
            "nonzero_dimension_marker": f"L24InitialReplay.records0.set {zero} (0, 1)",
            "wrong_destination": (f"L24InitialReplay.records0.set {negative} "
                                  f"({(destination + 1) % 860}, {rational(q)})"),
            "wrong_sign": (f"L24InitialReplay.records0.set {negative} "
                           f"({destination}, {rational([-q[0], q[1]])})"),
        }
        for name, value in changes.items():
            with self.subTest(name=name):
                self.prove(
                    f"def altered : List (Fin 860 × ℚ) := {value}\n"
                    "example : CotangentCombination.dimensionRecords L24InitialHints.columnIndex\n"
                    "    (Pi.single 0 1) L24Initial.pullback ≠\n"
                    "    (altered : Multiset (Fin 860 × ℚ)) := by\n"
                    "  rw [L24InitialReplay.records0_checked]\n  decide +kernel\n", name)

    def test_kernel_rejects_normalization_and_missing_permutation(self):
        self.prove(
            "example : L24InitialReplay.beforeAverageClaim ≠\n"
            "    (fun i ↦ 2 * L24InitialReplay.beforeAverageClaim i) := by\n"
            "  decide +kernel\n", "normalization")
        self.prove(
            "example : (1 / 5 : ℚ) * (∑ p : Fin 5,\n"
            "    L24InitialReplay.beforeAverageClaim\n"
            "      ((L24InitialGraphs.destination p.succ).symm 815)) ≠ 0 := by\n"
            "  decide +kernel\n", "omitted_identity_permutation")


if __name__ == "__main__":
    unittest.main(verbosity=2)
