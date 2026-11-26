"""Check complete descendant keys and reproducibility for the five canonical Bl₂ line requests."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_bl2_line_canonical import emit


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-bl2-line-canonical.json"
CLAIMS = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoLineCanonical.lean"
COMPARISON = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoLineCanonicalComparison.lean"


class CanonicalStrictLine(unittest.TestCase):
    def test_keyed_replay(self):
        original = REPORT.read_bytes()
        self.assertEqual(emit(original), CLAIMS.read_text())
        report = json.loads(original)
        report["cases"].reverse()
        marker = "@[expose] public section"
        reordered = emit(json.dumps(report).encode())
        self.assertEqual(reordered.split(marker)[1], emit(original).split(marker)[1])

    def test_frame_mutations(self):
        for mutation in ("same_energy", "wrong_psi", "swapped_marks", "exceptional", "omission"):
            with self.subTest(mutation=mutation):
                report = json.loads(REPORT.read_bytes())
                rows = report["cases"]
                if mutation == "same_energy":
                    rows[0]["class"] = [1, 0, 0]
                elif mutation == "wrong_psi":
                    rows[0]["powers"].reverse()
                elif mutation == "swapped_marks":
                    rows[0]["labels"].reverse()
                elif mutation == "exceptional":
                    rows[3]["labels"][0] = "E2"
                else:
                    rows.pop()
                with self.assertRaises(ValueError):
                    emit(json.dumps(report).encode())

    def test_each_ordinary_coefficient_is_bound(self):
        # Replay the real comparison proof with each incoming value changed in turn.
        marker = "@[expose] public section"
        comparison = COMPARISON.read_text()
        dependencies = [
            line for line in comparison.splitlines() if line.startswith("public import ")
            and line != "public import AxiomaticGW.GKM.Fixtures.BlowupTwoLineCanonical"
        ]
        proof = comparison.split(marker, 1)[1]
        for index in range(5):
            with self.subTest(index=index), tempfile.TemporaryDirectory() as directory:
                report = json.loads(REPORT.read_bytes())
                row = report["cases"][index]
                row["ordinary"] = [1, 19]
                row["equivariant"] = {"numerator": [[[0, 0], [1, 19]]],
                                      "denominator": [[[0, 0], [1, 1]]]}
                declarations = emit(json.dumps(report).encode()).replace(
                    "module\n", "module\n\n" + "\n".join(dependencies) + "\n", 1)
                path = Path(directory) / "Changed.lean"
                path.write_text(declarations + "\n" + proof)
                run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                     capture_output=True, timeout=180)
                diagnostics = run.stdout + run.stderr
                self.assertNotEqual(run.returncode, 0, diagnostics)
                self.assertIn("false", diagnostics.lower(), diagnostics)


if __name__ == "__main__":
    unittest.main()
