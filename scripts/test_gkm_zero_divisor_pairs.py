"""Replay native divisor checkpoints and distinguish ordinary from equivariant agreement."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from gkm_zero_divisor_checkpoints import (archive, assemble, class_frame, ingest, partial_source,
                                          path_for, read_partial, replay_completed, snapshot, store)
from gkm_zero_divisor_pairs import FRAMES, emit, requests


ROOT = Path(__file__).resolve().parents[1]
REPORTS = {"X1": "gkm-zero-divisor-f1.json", "X2": "gkm-zero-divisor-bl2.json"}


def encoded(report):
    return (json.dumps(report, sort_keys=True, indent=2) + "\n").encode()


def kernel_check(source):
    with tempfile.TemporaryDirectory() as directory:
        claim = Path(directory) / "DivisorFrame.lean"
        claim.write_text(source)
        return subprocess.run(["lake", "env", "lean", str(claim)], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)


class ZeroDivisorFrames(unittest.TestCase):
    def report(self, target):
        return (ROOT / "environments" / REPORTS[target]).read_bytes()

    def test_exact_held_frames(self):
        for target, size in (("X1", 20),):
            with self.subTest(target=target):
                raw = self.report(target)
                source = (ROOT / "AxiomaticGW/GKM/Fixtures" / (FRAMES[target][1] + ".lean"))
                self.assertEqual(emit(raw, target), source.read_text())
                self.assertEqual(len(requests(target)[target]), size)
                report = json.loads(raw)
                report["cases"].reverse()
                self.assertEqual(emit(encoded(report), target).split("@[expose]", 1)[1],
                                 source.read_text().split("@[expose]", 1)[1])

    def test_checkpoint_coverage_and_agreement(self):
        raw = self.report("X1")
        report = json.loads(raw)
        full = requests("X1")
        classes = sorted({q[0] for q in full["X1"]})
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / "combined.json"
            for beta in classes:
                frame = class_frame(full, "X1", beta)
                subset = dict(report, cases=[r for r in report["cases"] if tuple(r["class"]) == beta])
                part = path_for(root, "X1", beta)
                if beta == classes[-1]:
                    snapshot = root / "Completed.lean"
                    replay_completed("X1", full, classes, root, snapshot)
                    verified = kernel_check(snapshot.read_text())
                    self.assertEqual(verified.returncode, 0, verified.stdout)
                    with self.assertRaisesRegex(ValueError, "checkpoint still required"):
                        assemble("X1", full, classes, root, out)
                store(part, encoded(subset), frame, "X1")
            assemble("X1", full, classes, root, out)
            self.assertEqual(out.read_bytes(), raw)
            original = part.read_bytes()
            changed = json.loads(original)
            frac = changed["cases"][0]["equivariant"]
            frac["denominator"] = [[[0, 0], [1, 1]], [[1, 0], [1, 1]]]
            store(part, encoded(changed), frame, "X1")
            self.assertEqual(part.read_bytes(), original)
            frac["numerator"] = [[[1, 0], [1, 1]]]
            with self.assertRaisesRegex(ValueError, "Conflicting native computations"):
                store(part, encoded(changed), frame, "X1")

    def test_partial_archive_survives_a_fresh_checkout(self):
        raw = (ROOT / "environments/gkm-zero-divisor-bl2-partial.json").read_bytes()
        report, rows = read_partial(raw, "X2")
        self.assertGreater(len(rows), 0)
        self.assertLess(len(rows), 180)
        self.assertEqual(report["kind"], "gkm_localization.zero_divisor_pairs.X2.partial")
        source = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoZeroDivisorPairsPartial.lean"
        self.assertEqual(partial_source(raw, "X2"), source.read_text())
        with self.assertRaisesRegex(ValueError, "Wrong schema"):
            emit(raw, "X2")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            full = requests("X2")
            classes = sorted({q[0] for q in full["X2"]})
            ingest(raw, "X2", full, root)
            self.assertEqual(snapshot("X2", full, classes, root), raw)
            actual = [b for b in classes if path_for(root, "X2", b).exists()]
            self.assertEqual(actual, [tuple(b) for b in report["coverage"]["complete_classes"]])
            target = root / "snapshot.json"
            archive("X2", full, classes, root, target)
            path_for(root, "X2", actual[0]).unlink()
            with self.assertRaisesRegex(ValueError, "discard or change"):
                archive("X2", full, classes, root, target)
            self.assertEqual(target.read_bytes(), raw)

    def test_partial_rejects_false_class_coverage(self):
        raw = (ROOT / "environments/gkm-zero-divisor-bl2-partial.json").read_bytes()
        for change, error in ((lambda r: r["cases"].pop(), "Incomplete or duplicate"),
                              (lambda r: r["coverage"]["complete_classes"].append([9, 9, 9]),
                               "distinct, proper benchmark classes"),
                              (lambda r: r["coverage"].update(benchmark_rows=179), "Wrong benchmark"),
                              (lambda r: r.update(kind="gkm_localization.zero_divisor_pairs.X2"),
                               "Wrong schema")):
            report = json.loads(raw)
            change(report)
            with self.assertRaisesRegex(ValueError, error):
                read_partial(encoded(report), "X2")
        incoming = json.loads(raw)
        incoming["cases"].reverse()
        self.assertEqual(read_partial(encoded(incoming), "X2")[1], read_partial(raw, "X2")[1])

    def test_missing_ordered_request(self):
        for target in ("X1",):
            with self.subTest(target=target):
                report = json.loads(self.report(target))
                report["cases"][0] = report["cases"][-1]
                with self.assertRaisesRegex(ValueError, "Incomplete or duplicate"):
                    emit(encoded(report), target)

    def test_fraction_field_and_regular_representatives(self):
        report = json.loads(self.report("X1"))
        claimed = report["cases"][0]["equivariant"]
        claimed["denominator"] = [[[0, 0], [1, 1]], [[1, 0], [1, 1]]]
        equivalent = kernel_check(emit(encoded(report), "X1"))
        self.assertEqual(equivalent.returncode, 0, equivalent.stdout)
        claimed["numerator"] = [[[1, 0], [1, 1]]]
        altered = kernel_check(emit(encoded(report), "X1"))
        self.assertNotEqual(altered.returncode, 0)
        self.assertIn("error:", altered.stdout)

    def test_coherent_wrong_divisor_value(self):
        report = json.loads(self.report("X1"))
        row = report["cases"][0]
        row["ordinary"] = [1, 1]
        row["equivariant"] = {"numerator": [[[0, 0], [1, 1]]],
                              "denominator": [[[0, 0], [1, 1]]]}
        source = emit(encoded(report), "X1").replace(
            "module\n", "module\npublic import AxiomaticGW.Surfaces.GenusTwoZeroDivisorPairs\n", 1)
        source += """
namespace AxiomaticGW.GKM.F1ZeroDivisorPairs
example : SurfaceGenusTwo.zeroDivisorPair? (requests 0) = some (values 0) := by decide +kernel
end AxiomaticGW.GKM.F1ZeroDivisorPairs
"""
        wrong = kernel_check(source)
        self.assertNotEqual(wrong.returncode, 0)
        self.assertIn("zeroDivisorPair? (requests 0)", wrong.stdout)


if __name__ == "__main__":
    unittest.main()
