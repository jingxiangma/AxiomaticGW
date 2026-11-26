"""Coverage and corruption checks for the held 48-query numerical comparison."""
import copy
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from gkm_plane_few_markings import (
    COMPUTATION_GROUPS, MANIFEST, REQUESTS, compare_candidates, emit, read_report,
    request_manifest, requests_source, split_sources,
)

ROOT = Path(__file__).resolve().parents[1]
GKM = ROOT / "environments/gkm-plane-genus-two-few-markings.json"
LEAN = ROOT / "environments/genus-two-plane-few-markings-native.json"
FRAME = ROOT / "AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneFewMarkingRequests.lean"
REPLAY = ROOT / "AxiomaticGW/GKM/Fixtures/PlaneGenusTwoFewMarkingsReplay.lean"


class PlaneFewMarkings(unittest.TestCase):
    def test_held_domain_and_deterministic_frame(self):
        self.assertEqual(json.loads(MANIFEST.read_bytes()), request_manifest())
        self.assertEqual(len(REQUESTS["X0"]), 48)
        self.assertEqual(request_manifest()["counts_by_arity"], {"0": 0, "1": 3, "2": 45})
        self.assertEqual(FRAME.read_text(), requests_source())
        for name, source in split_sources(GKM.read_bytes()).items():
            self.assertEqual(REPLAY.with_name(name).read_text(), source, name)

    def test_split_computation_preserves_every_claim(self):
        sources = split_sources(GKM.read_bytes())
        indices = []
        for name, start, stop in COMPUTATION_GROUPS:
            source = sources["PlaneGenusTwoFewMarkings" + name + ".lean"]
            actual = [int(i) for i in re.findall(r"private theorem value_(\d+)", source)]
            self.assertEqual(actual, list(range(start, stop)))
            indices.extend(actual)
            for i in actual:
                self.assertIn(f"(requests {i}) = some (values {i}) := by", source)
                if start != 0:
                    self.assertIn(f"exact PlaneGenusTwoAncestors.cached_computation {i}", source)
        self.assertEqual(indices, list(range(48)))
        assembly = sources[REPLAY.name]
        self.assertIn("canonicalValues = GenusTwoPlaneLine.values := rfl", assembly)
        self.assertIn("GenusTwoPlaneLine.accepted", assembly)
        self.assertIn("planeQueryValue? (requests i) = some (values i)", assembly)

    def test_actual_kernel_binding(self):
        original = GKM.read_bytes()
        corrupt = json.loads(original)
        corrupt["cases"][0]["ordinary"] = [1, 1]
        corrupt["cases"][0]["equivariant"] = {
            "numerator": [[[0, 0], [1, 1]]], "denominator": [[[0, 0], [1, 1]]]}
        changed = (json.dumps(corrupt, sort_keys=True, indent=2) + "\n").encode()
        # Exact rational coherence passes; the Lean computation must reject the false value.
        read_report(changed)
        for accepted, raw in [(True, original), (False, changed)]:
            with self.subTest(accepted=accepted), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / "PlaneFewMarkingClaim.lean"
                source.write_text(emit(raw, cached=True))
                result = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                                        text=True, capture_output=True, timeout=180)
                if accepted:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("Tactic `decide` failed", result.stdout + result.stderr)
                    self.assertIn("values i = PlaneGenusTwoFewMarkingsReplay.values i",
                                  result.stdout + result.stderr)
                    # Kernel rejection may print the meta reducer's stuck-Rat
                    # diagnostic. Independently prove that the changed value
                    # really differs; do not rely on that diagnostic's wording.
                    prefix = emit(raw, cached=True).split("/-- Bind every complete", 1)[0]
                    source.write_text(prefix +
                        "example : values 0 ≠ PlaneGenusTwoFewMarkingsReplay.values 0 := by\n"
                        "  decide +kernel\n"
                        "end AxiomaticGW.GKM.PlaneGenusTwoFewMarkingsClaim\n")
                    distinct = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                                              text=True, capture_output=True, timeout=180)
                    self.assertEqual(distinct.returncode, 0, distinct.stdout + distinct.stderr)

    def test_complete_native_comparison(self):
        self.assertEqual(compare_candidates(LEAN.read_bytes(), GKM.read_bytes()), 48)
        reordered = json.loads(LEAN.read_bytes())
        reordered["cases"].reverse()
        self.assertEqual(compare_candidates(json.dumps(reordered), GKM.read_bytes()), 48)

    def test_gkm_request_and_provenance_corruptions(self):
        original = json.loads(GKM.read_bytes())
        mutations = [
            lambda r: r["cases"][0].update(genus=1),
            lambda r: r["cases"][0].update(**{"class": [2]}),
            lambda r: r["cases"][0].update(powers=[4]),
            lambda r: r["cases"][0].update(labels=["pt"]),
            lambda r: r["cases"].pop(),
            lambda r: r["cases"].append(copy.deepcopy(r["cases"][0])),
            lambda r: r.update(input_sha256="0" * 64),
            lambda r: r.update(online_lookup=True),
            lambda r: r["source"].update(revision="0" * 40),
            lambda r: r["environment"].update(sage="changed"),
            lambda r: r["cases"][0].update(ordinary=[1, 1]),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                changed = copy.deepcopy(original)
                mutate(changed)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(changed))

    def test_lean_request_and_value_corruptions(self):
        original = json.loads(LEAN.read_bytes())
        mutations = [
            lambda r: r.update(positive_energy_bound=5),
            lambda r: r.update(maximum_markings=1),
            lambda r: r["cases"][0].update(target="X1"),
            lambda r: r["cases"][0].update(**{"class": [True]}),
            lambda r: r["cases"][0].update(powers=[0]),
            lambda r: r["cases"][0].update(ordinary=[1, 1]),
            lambda r: r["cases"][0].update(ordinary=[1, -128]),
            lambda r: r["cases"].pop(),
            lambda r: r["cases"].append(copy.deepcopy(r["cases"][0])),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                changed = copy.deepcopy(original)
                mutate(changed)
                with self.assertRaises(ValueError):
                    compare_candidates(json.dumps(changed), GKM.read_bytes())


if __name__ == "__main__":
    unittest.main()
