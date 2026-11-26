"""Check internal degree-five coverage and reject a false lower-genus support value."""

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import export_plane_genus_two_support as support


class PlaneGenusTwoSupport(unittest.TestCase):
    def test_complete_support_and_unchanged_benchmarks(self):
        for path, content in support.outputs().items():
            self.assertEqual(path.read_text(), content)
        report = json.loads(support.MANIFEST.read_text())
        for genus, case in enumerate(report["cases"]):
            self.assertEqual(case["energy_bound"], 15)
            self.assertEqual([r["curve"] for r in case["rows"]], [[d] for d in range(6)])
            old = json.loads([support.rational.MANIFEST, support.elliptic.MANIFEST][genus]
                             .read_text())["cases"][0]
            self.assertEqual(old["energy_bound"], 12)
            self.assertEqual(case["rows"][:5], old["rows"])

    def test_invalid_bound(self):
        for bound in [-1, True, 15.0]:
            with self.subTest(bound=bound), self.assertRaises(ValueError):
                support.rational.bounded("P2", bound)

    def test_kernel_rejects_changed_quintic_value(self):
        good = json.loads(support.MANIFEST.read_text())["cases"][0]
        bad = copy.deepcopy(good)
        bad["rows"][5]["value"][0] += 1
        for accepted, case in [(True, good), (False, bad)]:
            with self.subTest(accepted=accepted), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "SupportClaim.lean"
                path.write_text(support.rational.lean_module(case, "regression",
                                namespace="PlaneSupportRegression"))
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=support.ROOT,
                                        text=True, capture_output=True, timeout=180)
                if accepted:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("false", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
