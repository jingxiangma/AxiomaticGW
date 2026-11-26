"""Check the fiber singletons against the held full request frame and actual Lean reconstruction."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from genus_two_few_marking_requests import requests_for
from gkm_f1_fiber_one_marking import REQUESTS, emit

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-f1-fiber-one-marking.json"
FIXTURE = ROOT / "AxiomaticGW/GKM/Fixtures/F1FiberOneMarkingReplay.lean"


class FiberOneMarkingTests(unittest.TestCase):
    def test_determinism_and_full_class(self):
        raw = REPORT.read_bytes()
        source = emit(raw)
        self.assertEqual(source, FIXTURE.read_text())
        fiber = [q for q in requests_for("X1") if q[0] == (0, 1)]
        self.assertEqual(len(fiber), 68)
        self.assertEqual(REQUESTS["X1"], [q for q in fiber if len(q[1]) == 1])
        self.assertEqual(len(REQUESTS["X1"]), 4)
        report = json.loads(raw)
        report["cases"].reverse()
        self.assertEqual(source.split("-/", 1)[1], emit(json.dumps(report).encode()).split("-/", 1)[1])
        report["cases"][0]["class"] = [2, 0]
        with self.assertRaisesRegex(ValueError, "Changed request"):
            emit(json.dumps(report).encode())

    def test_nonzero_point_depends_on_reconstruction(self):
        report = json.loads(REPORT.read_bytes())
        point = next(c for c in report["cases"] if c["labels"] == ["pt"])
        self.assertEqual(point["ordinary"], [1, 240])
        point["ordinary"] = [0, 1]
        point["equivariant"]["numerator"] = []
        # The modified fraction is regular with the proposed ordinary value.
        # Only the independent geometric-algorithm comparison should fail.
        source = emit(json.dumps(report).encode())
        with tempfile.TemporaryDirectory(prefix="gw-fiber-singleton-") as folder:
            path = Path(folder) / "Changed.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                    capture_output=True, timeout=120)
            diagnostics = result.stdout + result.stderr
            self.assertNotEqual(result.returncode, 0, diagnostics)
            expected_line = next(i for i, line in enumerate(source.splitlines(), 1)
                                 if line == "  fin_cases j <;> decide +kernel")
            self.assertEqual(diagnostics.count("error:"), 1, diagnostics)
            self.assertIn(f"Changed.lean:{expected_line}:", diagnostics)
            self.assertIn("false", diagnostics.lower())


if __name__ == "__main__":
    unittest.main()
