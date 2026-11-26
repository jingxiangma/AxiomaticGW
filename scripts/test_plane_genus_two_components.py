#!/usr/bin/env python3
"""Exercise component exchange and actual kernel rejection of false values."""
import copy
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from export_plane_genus_two_components import (NAMESPACE, POINT, PREFIX, SELECTIONS,
                                              component_keys, key, read_report,
                                              read_selections, sources)

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-plane-component-candidates.json"


class ComponentExchangeTests(unittest.TestCase):
    def test_complete_keys_and_generation(self):
        raw = REPORT.read_bytes()
        report = read_report(raw)
        self.assertEqual(len(report["components"]), 291)
        self.assertEqual({r["index"] for r in report["rows"]}, set(range(6, 39)))
        self.assertEqual(set().union(*(component_keys(r) for r in report["rows"])),
                         {key(r["key"]) for r in report["components"]})
        outputs = sources(raw)
        for name, text in outputs.items():
            self.assertEqual((ROOT / "AxiomaticGW/GKM/Fixtures" / name).read_text(), text)
            self.assertNotIn("native_decide", text)
            self.assertTrue(all(len(line) <= 100 for line in text.splitlines()), name)
        self.assertEqual(sum(text.count("theorem value_") for name, text in outputs.items()
                             if name.startswith(PREFIX + "Genus")), 291)

    def test_malformed_records_rejected(self):
        original = json.loads(REPORT.read_bytes())
        mutations = []
        for mutate in [
            lambda r: r.update(schema_version=True),
            lambda r: r.update(proof_status="accepted"),
            lambda r: r["rows"].pop(),
            lambda r: r["rows"].append(copy.deepcopy(r["rows"][0])),
            lambda r: r["rows"][0].update(index=False),
            lambda r: r["components"].pop(),
            lambda r: r["components"].append(copy.deepcopy(r["components"][0])),
            lambda r: r["components"][0]["key"].__setitem__(0, True),
            lambda r: r["components"][0]["key"].__setitem__(1, 2),
            lambda r: r["components"][0]["key"].__setitem__(2, 9),
            lambda r: r["components"][0]["key"].__setitem__(3, 7),
            lambda r: r["components"][0].update(value=[1, 0]),
            lambda r: r["components"][0].update(value=[1.0, 2]),
            lambda r: r["rows"][0]["symbolic_terms"][0].update(coefficient=[0, 1]),
        ]:
            changed = copy.deepcopy(original)
            mutate(changed)
            mutations.append(changed)
        for i, report in enumerate(mutations):
            with self.subTest(case=i), self.assertRaises(ValueError):
                read_report(json.dumps(report).encode())
        duplicate = REPORT.read_text().replace('"schema_version":1',
                                               '"schema_version":1,"schema_version":1', 1)
        with self.assertRaises(ValueError):
            read_report(duplicate.encode())

    def test_component_selection_integrity_and_partial_fallback(self):
        rows = sorted(read_report(REPORT.read_bytes())["components"], key=lambda r: r["key"])
        original = json.loads(SELECTIONS.read_bytes())
        self.assertEqual(len(read_selections(SELECTIONS.read_bytes(), rows)), 56)
        for mutate in [
            lambda r: r.update(schema_version=True),
            lambda r: r.update(proof_status="proved"),
            lambda r: r["rows"].pop(),
            lambda r: r["rows"].append(copy.deepcopy(r["rows"][0])),
            lambda r: r["rows"][0].update(index=False),
            lambda r: r["rows"][0].update(component=rows[0]["key"]),
            lambda r: r["rows"][0]["keys"].append(copy.deepcopy(r["rows"][0]["keys"][0])),
            lambda r: r["rows"][0].update(keys=[r["rows"][0]["component"]]),
        ]:
            changed = copy.deepcopy(original)
            mutate(changed)
            with self.assertRaises(ValueError):
                read_selections(json.dumps(changed), rows)
        partial = copy.deepcopy(original)
        partial["rows"][0]["keys"] = []
        self.assertEqual(read_selections(json.dumps(partial), rows)[partial["rows"][0]["index"]], [])

    def check_kernel(self, source, valid):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "IncomingComponents.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    capture_output=True, text=True)
            if valid:
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            else:
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("error", result.stdout + result.stderr)

    def test_kernel_rejects_false_nonzero_component(self):
        original = json.loads(REPORT.read_bytes())
        selected = component_keys(next(r for r in original["rows"] if r["index"] == 12))
        held = sorted((r for r in original["components"] if key(r["key"]) in selected),
                      key=lambda r: r["key"])[0]["key"]
        changed = copy.deepcopy(original)
        next(r for r in changed["components"] if r["key"] == held)["value"] = [2, 1]
        for valid, report in [(True, original), (False, changed)]:
            with self.subTest(valid=valid):
                raw = json.dumps(report).encode()
                read_report(raw)  # Candidate arithmetic does not authorize the new value.
                source = sources(raw)[POINT + ".lean"].split("private theorem value_1 :", 1)[0]
                source += "\nend AxiomaticGW.GKM." + POINT + "\n"
                self.check_kernel(source, valid)

    def test_kernel_rejects_false_dimension_zero(self):
        original = json.loads(REPORT.read_bytes())
        rows = sorted(original["components"], key=lambda r: r["key"])
        selected = component_keys(next(r for r in original["rows"] if r["index"] == 12))
        i = next(i for i, row in enumerate(rows)
                 if key(row["key"])[0] == 1 and key(row["key"]) not in selected and
                 sum(k for _, k in key(row["key"])[2]) > len(key(row["key"])[2]))
        held = rows[i]["key"]
        degree = sum(held[3::2])
        changed = copy.deepcopy(original)
        next(r for r in changed["components"] if r["key"] == held)["value"] = [1, 1]
        for valid, report in [(True, original), (False, changed)]:
            with self.subTest(valid=valid):
                raw = json.dumps(report).encode()
                read_report(raw)
                outputs = sources(raw)
                group = outputs[PREFIX + f"Genus1Psi{degree}.lean"]
                proof = re.search(rf"theorem value_{i} :[\s\S]*?(?=\n\n)", group).group()
                source = outputs[PREFIX + "Data.lean"]
                source += ("\nnamespace " + NAMESPACE + "\nopen SurfaceGenusTwo\n" + proof +
                           "\nend " + NAMESPACE + "\n")
                self.check_kernel(source, valid)


if __name__ == "__main__":
    unittest.main()
