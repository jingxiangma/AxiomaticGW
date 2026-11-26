"""Exercise the complete ordered energy-one frame and its native report replay."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_two_positive_pairs import emit


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-positive-pairs.json"
CLAIMS = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoPositivePairClaims.lean"


class PositivePairs(unittest.TestCase):
    def test_complete_frame_and_replay(self):
        raw = REPORT.read_bytes()
        self.assertEqual(emit(raw), CLAIMS.read_text())
        cases = json.loads(raw)["cases"]
        self.assertEqual(len(cases), 57)
        self.assertEqual(sum(c["ordinary"][0] != 0 for c in cases), 28)
        keyed = {(c["target"], tuple(c["class"]), tuple(c["labels"])): c for c in cases}
        for (target, beta, labels), case in keyed.items():
            reverse = keyed[target, beta, labels[::-1]]
            self.assertEqual(case["ordinary"], reverse["ordinary"])
            self.assertEqual(case["powers"], reverse["powers"][::-1])

    def test_query_identity(self):
        for field, new in (("powers", [1, 2]), ("class", [1, 0, 0]), ("labels", ["H", "unit"])):
            data = json.loads(REPORT.read_bytes())
            row = next(c for c in data["cases"] if c["class"] == [0, 0, 1] and c["labels"] == ["unit", "E2"])
            row[field] = new
            with self.subTest(field=field), self.assertRaises(ValueError):
                emit(json.dumps(data).encode())

    def test_kernel_rejects_changed_exceptional_product(self):
        data = json.loads(REPORT.read_bytes())
        row = next(c for c in data["cases"] if c["target"] == "X1" and c["labels"] == ["E1", "E1"])
        self.assertEqual(row["ordinary"], [1, 144])
        row["ordinary"] = [1, 145]
        row["equivariant"] = {"numerator": [[[0, 0], [1, 145]]],
                              "denominator": [[[0, 0], [1, 1]]]}
        source = emit(json.dumps(data).encode()).replace(
            "public import AxiomaticGW.Surfaces.Queries",
            "public import AxiomaticGW.Surfaces.Fixtures.GenusTwoPositiveDivisorPairs")
        source += """
open AxiomaticGW AxiomaticGW.GKM.GenusTwoPositivePairs
example : SurfaceGenusTwoBlowupDescendants.queryValue? 0 (OneBlowup.requests 2 2) =
    some (OneBlowup.values 2 2) := by
  exact SurfaceGenusTwoPositiveDivisorPairs.HirzebruchOne.exceptionalPair_value
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Changed.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                    capture_output=True, timeout=150)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("type mismatch", result.stdout.lower())


if __name__ == "__main__":
    unittest.main()
