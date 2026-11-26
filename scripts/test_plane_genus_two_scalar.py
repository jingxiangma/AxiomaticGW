"""Held coverage, arithmetic and real Lean rejection for scalar table exchange."""

import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_plane_genus_two_scalar import emit, read_report

ROOT = Path(__file__).resolve().parents[1]


def line_candidates():
    """Finite test input; its values are certified separately by the Lean fixture."""
    requests = [
        {"genus": 2, "curve": [1], "insertions": [[2, 0]] * 4},
        {"genus": 2, "curve": [1], "insertions": [[1, 1]] + [[2, 0]] * 3},
        {"genus": 2, "curve": [1], "insertions": [[2, 1]] + [[2, 0]] * 2}]
    return {"schema_version": 1, "kind": "axiomatic_gw.plane_genus_two_scalar", "bound": 1,
            "initial": [[0, 1], [-1, 960], [0, 1]],
            "rows": [{"degree": 1, "requests": requests, "values": [[0, 1]] * 3,
                      "equations": [
                          {"family": i, "constant": c, "remainder": [0, 1],
                           "earlier_coefficients": [{"degree": 0, "family": 1,
                                                     "coefficient": [v, 1]}]}
                          for i, c, v in [(0, [1, 10], 96), (1, [1, 20], 48), (2, [1, 40], 24)]]}]}


class PlaneScalarExchange(unittest.TestCase):
    def test_deterministic_export_and_complete_zero_rows(self):
        raw = json.dumps(line_candidates()).encode()
        report, values = read_report(raw, 1)
        self.assertEqual(len(report["rows"]), 1)
        self.assertEqual(values[1], [0, 0, 0])
        self.assertEqual(emit(raw, 1), emit(raw, 1))
        self.assertIn("theorem coverage", emit(raw, 1))
        self.assertIn("theorem claims", emit(raw, 1))

    def test_corruptions_rejected_before_replay(self):
        changes = [
            lambda p: p.update(bound=0),
            lambda p: p["initial"].__setitem__(1, [0, 1]),
            lambda p: p["rows"].clear(),
            lambda p: p["rows"].append(copy.deepcopy(p["rows"][0])),
            lambda p: p["rows"][0].update(degree=2),
            lambda p: p["rows"][0]["requests"][0].update(genus=1),
            lambda p: p["rows"][0]["requests"][1].update(curve=[2]),
            lambda p: p["rows"][0]["requests"][1]["insertions"][0].__setitem__(0, True),
            lambda p: p["rows"][0]["requests"][1]["insertions"].reverse(),
            lambda p: p["rows"][0]["equations"].pop(),
            lambda p: p["rows"][0]["equations"][0]["earlier_coefficients"].clear(),
            lambda p: p["rows"][0]["equations"][0].update(remainder=[1, 1]),
            lambda p: p["rows"][0]["equations"][0].update(constant=[2, 20]),
            lambda p: p["rows"][0]["values"].__setitem__(0, [1, 1])]
        for index, change in enumerate(changes):
            with self.subTest(index=index):
                candidate = line_candidates()
                change(candidate)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(candidate), 1)

    def test_kernel_rejects_a_coherently_forged_equation(self):
        good = line_candidates()
        bad = copy.deepcopy(good)
        bad["rows"][0]["equations"][0].update(constant=[11, 10], remainder=[1, 1])
        bad["rows"][0]["values"] = [[-1, 36], [-1, 12], [-1, 12]]
        # This is an internally consistent different linear system. Its original BP scalar is false.
        read_report(json.dumps(bad), 1)
        for expected, report in [(True, good), (False, bad)]:
            with self.subTest(accepted=expected), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "ScalarClaim.lean"
                path.write_text(emit(json.dumps(report).encode(), 1))
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=180)
                if expected:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("11 / 10", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
