"""Check the 17-row report, both exceptional coordinates and adversarial ordinary values."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_two_one_marking import claims

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-one-marking.json"
MODULES = ROOT / "AxiomaticGW/GKM/Fixtures"
CONSUMER = MODULES / "GenusTwoOneMarkingReplay.lean"


def encoded(report):
    return json.dumps(report, sort_keys=True).encode()


class OneMarkingComparison(unittest.TestCase):
    def test_export(self):
        raw = REPORT.read_bytes()
        self.assertEqual(claims(raw), (MODULES / "GenusTwoOneMarkingClaims.lean").read_text())
        report = json.loads(raw)
        self.assertEqual(len(report["cases"]), 17)
        report["cases"].reverse()
        marker = "@[expose] public section"
        self.assertEqual(claims(raw).split(marker)[1], claims(encoded(report)).split(marker)[1])

    def test_full_class_and_marking(self):
        for field, value in (("class", [0, 0, 1]), ("powers", [4]), ("labels", ["E3"])):
            with self.subTest(field=field):
                report = json.loads(REPORT.read_bytes())
                row = next(c for c in report["cases"] if c["target"] == "X2")
                row[field] = value
                with self.assertRaises(ValueError):
                    claims(encoded(report))

    def test_kernel_rejects_coherent_changes(self):
        consumer = CONSUMER.read_text()
        imports = [line.replace("public import ", "import ", 1) for line in consumer.splitlines()
                   if line.startswith("public import ") and not line.endswith("OneMarkingClaims")]
        marker = "namespace AxiomaticGW.GKM.GenusTwoOneMarking"
        body = marker + consumer.split(marker, 1)[1]
        for target in (None, "X0", "X1", "X2"):
            with self.subTest(changed_target=target), tempfile.TemporaryDirectory() as temporary:
                report = json.loads(REPORT.read_bytes())
                if target:
                    row = next(c for c in report["cases"] if c["target"] == target and c["labels"] == ["unit"])
                    row["equivariant"] = {"numerator": [], "denominator": [[[0, 0], [1, 1]]]}
                    row["ordinary"] = [0, 1]
                data = claims(encoded(report)).split(marker, 1)[1]
                path = Path(temporary) / "Comparison.lean"
                path.write_text("\n".join(imports) + "\n" + marker + data + "\n" + body)
                run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                     capture_output=True, timeout=120)
                if target is None:
                    self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                else:
                    self.assertNotEqual(run.returncode, 0)
                    self.assertIn("false", run.stdout.lower())


if __name__ == "__main__":
    unittest.main()
