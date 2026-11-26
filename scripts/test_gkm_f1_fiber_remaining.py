"""Regression checks for the three exact F1 fiber requests and their incoming values."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_f1_fiber_remaining import emit

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-f1-fiber-remaining.json"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupF1FiberRemainingReplay.lean"


def encoded(report):
    return (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()


class FiberReplay(unittest.TestCase):
    def test_keyed_replay(self):
        raw = REPORT.read_bytes()
        self.assertEqual(emit(raw), REPLAY.read_text())
        report = json.loads(raw)
        report["cases"].reverse()
        # Reordering rows changes the report digest only.
        payload = lambda data: emit(data).split("@[expose] public section", 1)[1]
        self.assertEqual(payload(raw), payload(encoded(report)))

    def test_full_frame(self):
        for mutation in ("same_energy", "wrong_powers", "wrong_state", "duplicate", "omitted"):
            with self.subTest(mutation=mutation):
                report = json.loads(REPORT.read_bytes())
                rows = report["cases"]
                if mutation == "same_energy":
                    rows[0]["class"] = [2, 0]
                elif mutation == "wrong_powers":
                    rows[0]["powers"].reverse()
                elif mutation == "wrong_state":
                    rows[2]["labels"][0] = "H"
                elif mutation == "duplicate":
                    rows[2] = rows[0]
                else:
                    rows.pop()
                with self.assertRaises(ValueError):
                    emit(encoded(report))

    def test_kernel_binding(self):
        raw = REPORT.read_bytes()
        source = emit(raw)
        controls = [("positive", source, True)]
        for index in range(3):
            report = json.loads(raw)
            claim = report["cases"][index]
            claim["ordinary"] = [7, 19]
            claim["equivariant"] = {"numerator": [[[0, 0], [7, 19]]],
                                    "denominator": [[[0, 0], [1, 1]]]}
            controls.append((f"wrong_value_{index}", emit(encoded(report)), False))
        for name, old, new in [("same_energy", "![0, 1]", "![2, 0]"),
                               ("wrong_state", "[⟨.exceptional 0, 1⟩", "[⟨.hyperplane, 1⟩"),
                               ("wrong_order", "[⟨.point, 1⟩, ⟨.point, 0⟩]",
                                "[⟨.point, 0⟩, ⟨.point, 1⟩]")]:
            self.assertIn(old, source)
            controls.append((name, source.replace(old, new, 1), False))
        for name, claim, valid in controls:
            with self.subTest(case=name), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "Claim.lean"
                path.write_text(claim)
                run = subprocess.run(["lake", "env", "lean", "--memory=2048", str(path)],
                                     cwd=ROOT, text=True, capture_output=True, timeout=120)
                diagnostics = run.stdout + run.stderr
                if valid:
                    self.assertEqual(run.returncode, 0, diagnostics)
                else:
                    self.assertNotEqual(run.returncode, 0, diagnostics)
                    if name.startswith("wrong_value_"):
                        self.assertIn("⊢ False", diagnostics, diagnostics)
                    else:
                        self.assertIn("false", diagnostics, diagnostics)


if __name__ == "__main__":
    unittest.main()
