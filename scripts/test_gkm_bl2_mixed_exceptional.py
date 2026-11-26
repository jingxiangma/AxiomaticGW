"""Exercise the complete ordered E₁+E₂ native packet before Lean reconstruction."""
from collections import Counter
import json
from pathlib import Path
import unittest

from gkm_bl2_mixed_exceptional import REQUESTS, emit


class MixedExceptionalPacket(unittest.TestCase):
    root = Path(__file__).resolve().parents[1]
    packet = root / "environments/gkm-bl2-mixed-exceptional.json"
    fixture = root / "AxiomaticGW/GKM/Fixtures/BlowupTwoMixedExceptional.lean"

    def test_native_order_and_regeneration(self):
        raw = self.packet.read_bytes()
        self.assertEqual(Counter(len(p) for _, p, _ in REQUESTS["X2"]), {1: 5, 2: 100})
        self.assertEqual(emit(raw), self.fixture.read_text())
        data = json.loads(raw)
        data["cases"].reverse()
        self.assertEqual(emit(json.dumps(data).encode()).split("-/", 1)[1],
                         self.fixture.read_text().split("-/", 1)[1])

    def test_repeated_or_different_full_class(self):
        data = json.loads(self.packet.read_bytes())
        data["cases"][0]["class"] = [2, 0, 0]
        with self.assertRaisesRegex(ValueError, "Changed request"):
            emit(json.dumps(data).encode())
        data["cases"][0] = data["cases"][1]
        with self.assertRaises(ValueError):
            emit(json.dumps(data).encode())


if __name__ == "__main__":
    unittest.main()
