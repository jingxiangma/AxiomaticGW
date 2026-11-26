"""Validate both marking orders, distinguish the full curves, and reject a false dilaton factor."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_two_unit_pairs import emit


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-unit-pairs.json"
CLAIMS = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoUnitPairClaims.lean"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoUnitPairReplay.lean"
NAMESPACE = "namespace AxiomaticGW.GKM.GenusTwoUnitPairs"


class UnitPairs(unittest.TestCase):
    def test_all_cases_and_orders(self):
        raw = REPORT.read_bytes()
        self.assertEqual(emit(raw), CLAIMS.read_text())
        report = json.loads(raw)
        self.assertEqual(len(report["cases"]), 76)
        self.assertEqual(sum(row["ordinary"] != [0, 1] for row in report["cases"]), 40)
        report["cases"].reverse()
        self.assertEqual(emit(raw).split(NAMESPACE)[1],
                         emit(json.dumps(report).encode()).split(NAMESPACE)[1])

    def test_curve_and_cotangent_binding(self):
        for field, value in (("class", [0, 1, 0]), ("powers", [2, 0])):
            data = json.loads(REPORT.read_bytes())
            row = next(c for c in data["cases"] if c["class"] == [0, 0, 1] and
                       c["labels"] == ["unit", "H"] and c["powers"] == [1, 2])
            row[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                emit(json.dumps(data).encode())

    def test_kernel_rejects_missing_dilaton_factor(self):
        data = json.loads(REPORT.read_bytes())
        row = next(c for c in data["cases"] if c["class"] == [0, 0, 1] and
                   c["labels"] == ["unit", "H"] and c["powers"] == [1, 2])
        self.assertEqual(row["ordinary"], [1, 80])
        row["ordinary"] = [1, 240]
        row["equivariant"] = {"numerator": [[[0, 0], [1, 240]]],
                              "denominator": [[[0, 0], [1, 1]]]}
        replay = REPLAY.read_text()
        imports = [line.replace("public import", "import") for line in replay.splitlines()
                   if line.startswith("public import") and not line.endswith("GenusTwoUnitPairClaims")]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Changed.lean"
            path.write_text("\n".join(imports) + "\n" + NAMESPACE +
                            emit(json.dumps(data).encode()).split(NAMESPACE, 1)[1] + "\n" +
                            NAMESPACE + replay.split(NAMESPACE, 1)[1])
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                    capture_output=True, timeout=120)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("false", result.stdout.lower())


if __name__ == "__main__":
    unittest.main()
