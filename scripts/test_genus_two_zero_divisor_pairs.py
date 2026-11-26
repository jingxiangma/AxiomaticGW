#!/usr/bin/env python3
"""Cross-check the divisor routing predicate on every frozen ordered blowup request."""
import json
from pathlib import Path
import unittest

from genus_two_zero_divisor_pairs import accepts

FRAME = Path(__file__).resolve().parents[1] / "environments/genus-two-few-markings-requests.json"


class ZeroDivisorPairsTest(unittest.TestCase):
    def test_complete_manifests(self):
        for frame, counts, extras in zip(json.loads(FRAME.read_bytes())["targets"][1:],
                                         ((4, 4, 8, 4), (24, 42, 48, 66)),
                                         ((0, 0, 6, 2), (0, 28, 36, 52))):
            accepted = [0] * 4
            additional = [0] * 4
            for row in frame["requests"]:
                q = {**row, "insertions": list(zip(row["labels"], row["powers"]))}
                if not accepts(q):
                    continue
                beta = q["class"]
                energy = sum(a * w for a, w in zip(beta, frame["energy_weights"]))
                accepted[energy - 1] += 1
                known = (energy == 1 or (q["target"] == "X1" and energy == 2) or
                         (q["target"] == "X2" and beta == [1, 1, 0]) or
                         (beta[-1] == 0 and "pt" in q["labels"]))
                if not known:
                    additional[energy - 1] += 1
            self.assertEqual(tuple(accepted), counts)
            self.assertEqual(tuple(additional), extras)

    def test_first_divisor_and_signed_cup(self):
        query = {"target": "X2", "genus": 2, "class": [0, 1, 1]}
        for marks, expected in (
                ([["H", 3], ["E2", 0]], True),
                ([["E2", 0], ["H", 3]], True),
                ([["H", 3], ["E1", 0]], False),
                ([["E2", 3], ["E2", 0]], False),
                ([["E2", 0], ["unit", 1]], False),
                ([["E2", 0], ["E1", 0]], True),
                ([["E1", 0], ["E2", 0]], False)):
            self.assertEqual(accepts({**query, "insertions": marks}), expected)


if __name__ == "__main__":
    unittest.main()
