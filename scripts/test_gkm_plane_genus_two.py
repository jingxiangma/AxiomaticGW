"""Held-query and kernel-binding regressions for genus-two plane line replay."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_plane_genus_two import emit, read_report

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-plane-genus-two-line.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/PlaneGenusTwoLineReplay.lean"


class PlaneGenusTwoReplay(unittest.TestCase):
    def test_saved_report_and_deterministic_export(self):
        raw = REPORT.read_bytes()
        _, grouped = read_report(raw)
        self.assertEqual(len(grouped["X0"]), 3)
        self.assertFalse(grouped["X1"] or grouped["X2"])
        self.assertEqual(emit(raw), REPLAY.read_text())

    def test_request_and_provenance_rejections(self):
        original = json.loads(REPORT.read_bytes())
        mutations = [
            lambda r: r["cases"][0].update(genus=1),
            lambda r: r["cases"][0].update(**{"class": [2]}),
            lambda r: r["cases"][1].update(powers=[0, 1, 0, 0]),
            lambda r: r["cases"][1].update(labels=["pt", "H", "pt", "pt"]),
            lambda r: r["cases"].pop(),
            lambda r: r["cases"].append(copy.deepcopy(r["cases"][0])),
            lambda r: r.update(input_sha256="0" * 64),
            lambda r: r.update(online_lookup=True),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                report = copy.deepcopy(original)
                mutate(report)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(report))

    def test_actual_kernel_binding(self):
        original = REPORT.read_bytes()
        corrupt = json.loads(original)
        corrupt["cases"][0]["ordinary"] = [1, 1]
        corrupt["cases"][0]["equivariant"] = {
            "numerator": [[[0, 0], [1, 1]]], "denominator": [[[0, 0], [1, 1]]]}
        changed = (json.dumps(corrupt, sort_keys=True, indent=2) + "\n").encode()
        # Exact coefficient coherence still holds. Only the Lean proof rejects the answer.
        read_report(changed)
        for accepted, raw in [(True, original), (False, changed)]:
            with self.subTest(accepted=accepted), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / "PlaneClaim.lean"
                source.write_text(emit(raw))
                result = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=180)
                if accepted:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("false", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
