"""Check full class, marking order, and the nonzero H-square term of the genus-two divisor replay."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_two_divisor_pairs import emit


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-divisor-pairs.json"
CLAIMS = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoDivisorPairClaims.lean"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoDivisorPairReplay.lean"
NAMESPACE = "namespace AxiomaticGW.GKM.GenusTwoDivisorPairs"


class DivisorPairs(unittest.TestCase):
    def test_replay_and_coverage(self):
        raw = REPORT.read_bytes()
        self.assertEqual(emit(raw), CLAIMS.read_text())
        report = json.loads(raw)
        self.assertEqual(len(report["cases"]), 112)
        report["cases"].reverse()
        self.assertEqual(emit(raw).split(NAMESPACE, 1)[1],
                         emit(json.dumps(report).encode()).split(NAMESPACE, 1)[1])

    def test_other_curve_and_moved_power(self):
        for field, value in (("class", [1, 0, 0]), ("powers", [2, 0])):
            data = json.loads(REPORT.read_bytes())
            row = next(c for c in data["cases"] if c["class"] == [0, 0, 1] and
                       c["labels"] == ["H", "E1"] and c["powers"] == [0, 2])
            row[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                emit(json.dumps(data).encode())

    def test_kernel_rejects_omitted_point_term(self):
        data = json.loads(REPORT.read_bytes())
        row = next(c for c in data["cases"] if c["target"] == "X0" and
                   c["labels"] == ["H", "H"] and c["powers"] == [0, 4])
        self.assertEqual(row["ordinary"], [-1, 192])
        row["ordinary"] = [-1, 960]
        row["equivariant"] = {"numerator": [[[0, 0], [-1, 960]]],
                              "denominator": [[[0, 0], [1, 1]]]}
        replay = REPLAY.read_text()
        imports = [line.replace("public import", "import") for line in replay.splitlines()
                   if line.startswith("public import") and not line.endswith("GenusTwoDivisorPairClaims")]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Changed.lean"
            path.write_text("\n".join(imports) + "\n" + NAMESPACE +
                            emit(json.dumps(data).encode()).split(NAMESPACE, 1)[1] +
                            "\n" + NAMESPACE + replay.split(NAMESPACE, 1)[1])
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    capture_output=True, text=True, timeout=150)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("false", result.stdout.lower())


if __name__ == "__main__":
    unittest.main()
