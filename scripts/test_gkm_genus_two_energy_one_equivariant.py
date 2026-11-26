"""Check the exact indexed fractions, regular changes of representative and torus dependence."""
import copy
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from gkm_genus_two_energy_one_equivariant import emit

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/gkm-genus-two-energy-one.json"
FIXTURE = ROOT / "AxiomaticGW/GKM/Fixtures/GenusTwoEnergyOneEquivariant.lean"


def row(report, label, power):
    return next(c for c in report["cases"]
                if (c["target"], c["class"], c["labels"], c["powers"]) ==
                ("X1", [1, 0], [label], [power]))


def check_lean(directory, filename, source):
    path = Path(directory) / filename
    path.write_text(source)
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                            text=True, capture_output=True, timeout=150)
    return result.returncode, result.stdout + result.stderr


class EnergyOneEquivariantTests(unittest.TestCase):
    def test_deterministic_replay_and_order(self):
        raw = REPORT.read_bytes()
        source = emit(raw)
        self.assertEqual(source, FIXTURE.read_text())
        report = json.loads(raw)
        report["cases"].reverse()
        reordered = emit(json.dumps(report).encode())
        self.assertEqual(source.split("-/", 1)[1], reordered.split("-/", 1)[1])

    def test_regular_equivalence_and_same_ordinary_mutation(self):
        report = json.loads(REPORT.read_bytes())
        equivalent = copy.deepcopy(report)
        unit = row(equivalent, "unit", 3)
        q = unit["ordinary"]
        self.assertEqual(q, [13, 2880])
        # q(1+xy)/(1+xy) is the same rational function as q.
        unit["equivariant"] = {
            "numerator": [[[0, 0], q], [[1, 1], q]],
            "denominator": [[[0, 0], [1, 1]], [[1, 1], [1, 1]]],
        }
        different = copy.deepcopy(report)
        hyperplane = row(different, "H", 2)
        self.assertEqual(hyperplane["ordinary"], [0, 1])
        # xy/1 is regular and vanishes at zero. Its full field value changes.
        hyperplane["equivariant"]["numerator"] = [[[1, 1], [1, 1]]]
        source = emit(json.dumps(different).encode())
        # Independent kernel witness for this exact ordinary row and perturbation.
        witness = """
open AxiomaticGW.GKM.EquivariantCoefficients
open AxiomaticGW.GKM.GenusTwoEnergyOne.OneBlowup

example : Specializes (x * y) (values 1) := by
  rw [show values 1 = 0 by decide +kernel]
  have h := specializes_of_eq_polynomial (MvPolynomial.X 0 * MvPolynomial.X 1)
    (show x * y = embed _ by rw [map_mul, embed_X_zero, embed_X_one])
  simpa only [atZero, map_mul, MvPolynomial.eval₂Hom_X', Pi.zero_apply, zero_mul] using h

example : x * y ≠ (values 1 : Coefficient) := by
  rw [show values 1 = 0 by decide +kernel, Rat.cast_zero]
  exact mul_ne_zero x_ne_zero y_ne_zero
"""
        with tempfile.TemporaryDirectory(prefix="gw-energy-one-characters-") as directory:
            rc, diagnostic = check_lean(directory, "Regular.lean",
                                        emit(json.dumps(equivalent).encode()) + witness)
            self.assertEqual(rc, 0, diagnostic)
            rc, diagnostic = check_lean(directory, "Changed.lean", source)
            self.assertNotEqual(rc, 0)
            lines = source.splitlines()
            start = next(i for i, line in enumerate(lines, 1)
                         if line.startswith("theorem fraction_eq_constant"))
            end = next(i for i, line in enumerate(lines, 1) if i > start and line == "end")
            failures = re.findall(r"Changed\.lean:(\d+):\d+: error:", diagnostic)
            self.assertTrue(failures, diagnostic)
            self.assertTrue(all(start <= int(n) < end for n in failures), diagnostic)
            self.assertIn("unsolved goals", diagnostic)


if __name__ == "__main__":
    unittest.main()
