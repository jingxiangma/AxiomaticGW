"""Bind each of the 26 second-unit GKM rows to its ordered reconstructed query and value."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_genus_two_positive_pairs import emit


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-positive-pairs.json"


def comparison_source(raw):
    source = emit(raw).replace(
        "public import AxiomaticGW.Surfaces.Queries",
        "public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.OneBlowup\n"
        "public import AxiomaticGW.Surfaces.Fixtures.SecondUnitPairs.TwoBlowup",
    )
    checks = ["open AxiomaticGW AxiomaticGW.GKM.GenusTwoPositivePairs"]
    for native, reconstructed, size, start in (
        ("OneBlowup", "OneBlowup", 3, 0),
        ("ExceptionalOne", "TwoBlowup", 4, 0),
        ("ExceptionalTwo", "TwoBlowup", 4, 7),
        ("StrictLine", "TwoBlowup", 4, 14),
    ):
        pairs = [(0, k) for k in range(size)] + [(j, 0) for j in range(1, size)]
        lane = "GenusTwoSecondUnitPairs." + reconstructed
        for i, (j, k) in enumerate(pairs, start):
            checks.append(
                f"example : {native}.requests {j} {k} = {lane}.requests {i} ∧ "
                f"{native}.values {j} {k} = {lane}.values {i} := by decide +kernel"
            )
    return source + "\n" + "\n".join(checks) + "\n"


class SecondUnitPairs(unittest.TestCase):
    def test_every_claim_is_bound(self):
        original = REPORT.read_bytes()
        report = json.loads(original)
        changed = [row for row in report["cases"] if 2 in row["powers"]]
        self.assertEqual(len(changed), 26)
        for row in changed:
            row["ordinary"] = [1, 19]
            row["equivariant"] = {"numerator": [[[0, 0], [1, 19]]],
                                  "denominator": [[[0, 0], [1, 1]]]}
        for raw, errors in [(original, 0), (json.dumps(report).encode(), 26)]:
            with self.subTest(expected_errors=errors), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "Check.lean"
                path.write_text(comparison_source(raw))
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                        capture_output=True, timeout=180)
                log = result.stdout + result.stderr
                self.assertEqual(result.returncode == 0, errors == 0, log)
                diagnostics = [line for line in log.splitlines() if ": error:" in line]
                self.assertEqual(len(diagnostics), errors, log)
                if errors:
                    self.assertGreaterEqual(log.lower().count("false"), errors, log)


if __name__ == "__main__":
    unittest.main()
