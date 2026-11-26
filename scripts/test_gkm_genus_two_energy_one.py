"""Check the full primitive frame and its binding to the independently certified rows."""
import json
from pathlib import Path
import unittest

import gkm_genus_two_energy_one as native
from export_genus_two_energy_one_reductions import OUTPUT, selection_source, source

ROOT = Path(__file__).resolve().parents[1]


class PrimitiveFrame(unittest.TestCase):
    def setUp(self):
        self.raw = (ROOT / "environments/gkm-genus-two-energy-one.json").read_bytes()

    def test_exact_frame(self):
        self.assertEqual([len(native.REQUESTS[t]) for t in ("X0", "X1", "X2")], [0, 52, 240])
        generated = native.emit(self.raw)
        self.assertEqual(generated, (OUTPUT.parent / "GenusTwoEnergyOneClaims.lean").read_text())
        self.assertEqual(source(), OUTPUT.read_text())
        self.assertEqual(selection_source(), (OUTPUT.parent / "GenusTwoEnergyOneSelection.lean").read_text())

    def test_missing_and_moved_row(self):
        report = json.loads(self.raw)
        report["cases"].pop()
        with self.assertRaises(ValueError):
            native.emit(json.dumps(report).encode())
        report = json.loads(self.raw)
        row = next(c for c in report["cases"] if c["class"] == [1, 0, 0] and len(c["labels"]) == 2)
        row["class"] = [0, 1, 0]
        with self.assertRaises(ValueError):
            native.emit(json.dumps(report).encode())

    def test_reordered_report(self):
        report = json.loads(self.raw)
        report["cases"].reverse()
        # The report digest changes. Its two ordered arrays of mathematical data must agree.
        self.assertEqual(native.emit(self.raw).split("-/", 1)[1],
                         native.emit(json.dumps(report).encode()).split("-/", 1)[1])


if __name__ == "__main__":
    unittest.main()
