"""Check the full fixed query corpus, independently of numerical answers."""
from collections import Counter
import json
from pathlib import Path
import unittest

from genus_two_few_marking_requests import TARGETS, manifest, manifest_text

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "environments/genus-two-few-markings-requests.json"


class FewMarkingDomain(unittest.TestCase):
    def test_manifest_and_unchanged_plane_requests(self):
        report = manifest()
        self.assertEqual(MANIFEST.read_text(), manifest_text(report))
        self.assertEqual(json.loads(MANIFEST.read_text()), report)
        plane = json.loads((ROOT / "environments/genus-two-plane-few-markings-requests.json").read_text())
        self.assertEqual(report["targets"][0]["requests"], plane["requests"])
        self.assertEqual([t["request_count"] for t in report["targets"]], [48, 656, 4495])
        self.assertEqual(report["request_count"], 5199)

    def test_full_classes_and_closed_arity_counts(self):
        # Class counts are the coefficients of the fixed monoid generating functions.
        class_counts = {"X0": {3: 1}, "X1": {1: 1, 2: 2, 3: 2, 4: 3},
                        "X2": {1: 3, 2: 6, 3: 10, 4: 15}}
        for target in manifest()["targets"]:
            spec = TARGETS[target["target"]]
            queries = target["requests"]
            keys = [(tuple(q["class"]), tuple(q["powers"]), tuple(q["labels"])) for q in queries]
            self.assertEqual(len(keys), len(set(keys)))
            by_class = Counter((tuple(q["class"]), len(q["powers"])) for q in queries)
            classes = {beta for beta, _ in by_class}
            energies = {beta: sum(w*b for w, b in zip(spec["weights"], beta)) for beta in classes}
            self.assertEqual(dict(Counter(energies.values())), class_counts[target["target"]])
            states = len(spec["labels"])
            for beta, energy in energies.items():
                self.assertEqual(by_class[beta, 0], 0)
                self.assertEqual(by_class[beta, 1], states)
                # For fixed labels, k1+k2 = e+3-c1-c2 has e+4-c1-c2 solutions.
                # Each basis has mean codimension one, giving states²*(e+2).
                self.assertEqual(by_class[beta, 2], states**2 * (energy + 2))


if __name__ == "__main__":
    unittest.main()
