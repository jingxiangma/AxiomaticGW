"""Check strict-line request identity and reject a coherent but false incoming value."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_bl2_line_one_marking import emit


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-bl2-line-one-marking.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoLineOneMarkingReplay.lean"


class StrictLineOneMarking(unittest.TestCase):
    def test_saved_report_and_order(self):
        raw = REPORT.read_bytes()
        self.assertEqual(emit(raw), REPLAY.read_text())
        report = json.loads(raw)
        report["cases"].reverse()
        marker = "@[expose] public section"
        self.assertEqual(emit(raw).split(marker)[1], emit(json.dumps(report).encode()).split(marker)[1])

    def test_other_energy_one_class(self):
        report = json.loads(REPORT.read_bytes())
        report["cases"][0]["class"] = [1, 0, 0]
        with self.assertRaisesRegex(ValueError, "Changed request"):
            emit(json.dumps(report).encode())

    def test_kernel_rejects_coherent_zero(self):
        report = json.loads(REPORT.read_bytes())
        row = next(c for c in report["cases"] if c["labels"] == ["H"])
        row["ordinary"] = [0, 1]
        row["equivariant"] = {"numerator": [], "denominator": [[[0, 0], [1, 1]]]}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Changed.lean"
            path.write_text(emit(json.dumps(report).encode()))
            run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                 capture_output=True, timeout=120)
        self.assertNotEqual(run.returncode, 0)
        self.assertIn("false", run.stdout.lower())


if __name__ == "__main__":
    unittest.main()
