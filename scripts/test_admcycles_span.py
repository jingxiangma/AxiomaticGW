"""Replay the separating-edge consequence without Sage and reject a changed graph sign."""
from fractions import Fraction
from pathlib import Path
import subprocess
import tempfile
import unittest

from search_admcycles_span import source


class SeparatingDecoration(unittest.TestCase):
    def test_witness_and_target(self):
        weights = [Fraction(0), 0, 0, Fraction(1, 72), Fraction(-1, 72), 0, 0]
        root = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            for sign in [-1, 1]:
                with self.subTest(sign=sign):
                    target = [0, 0, 1, sign, 0, 0, 0, 0]
                    path = Path(directory) / "Relation.lean"
                    path.write_text(source(target, weights))
                    run = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                                         text=True, capture_output=True, timeout=90)
                    if sign == -1:
                        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                        self.assertIn(".evaluated' depends on axioms", run.stdout)
                    else:
                        self.assertNotEqual(run.returncode, 0)
                        self.assertIn("false", run.stdout.lower())
