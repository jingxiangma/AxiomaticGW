"""Pure integrity and coverage controls; deliberately launches no Lean process."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

parser = argparse.ArgumentParser()
parser.add_argument("--repository", type=Path, required=True)
parser.add_argument("--packet", type=Path, required=True)
parser.add_argument("--relabel-exporter", type=Path, required=True)
args, unittest_args = parser.parse_known_args()
path = Path(__file__).with_name("export_f1_root_zero_rows.py")
spec = importlib.util.spec_from_file_location("zero_exporter", path)
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)


class ZeroRowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw, cls.helper = exporter.checked_inputs(
            args.repository, args.packet, args.relabel_exporter)
        cls.source = cls.raw[exporter.SOURCE].decode()
        cls.claims = cls.raw[exporter.CLAIMS].decode()
        cls.packet = json.loads(cls.raw["packet"])
        cls.records, cls.groups = exporter.analyze(cls.source, cls.claims, cls.packet, cls.helper)

    def analyze(self, packet):
        return exporter.analyze(self.source, self.claims, packet, self.helper)

    def generate(self, output, repository=None, packet=None, helper=None):
        return exporter.generate(repository or args.repository, packet or args.packet,
                                 helper or args.relabel_exporter, output)

    def test_exact_original_815_partition(self):
        self.assertEqual(list(map(len, self.groups.values())), [3, 277, 414, 94, 27])
        all_indices = [i for group in self.groups.values() for i in group]
        self.assertEqual(sorted(all_indices), list(range(815)))
        self.assertEqual(len(set(all_indices)), 815)
        self.assertEqual(sorted(self.groups["coefficient_zero"] +
                                self.groups["nonzero_coefficient_genus_guard"]), list(range(121)))

    def test_zero_coordinate_precedes_overlapping_guard(self):
        self.assertTrue(self.packet["rows"][0]["genus_guard"])
        self.assertIn(0, self.groups["coefficient_zero"])
        self.assertNotIn(0, self.groups["nonzero_coefficient_genus_guard"])

    def test_sampled_slots_and_native_totals_are_ignored(self):
        packet = copy.deepcopy(self.packet)
        packet["total"] = "a false native total"
        for row in packet["rows"]:
            for key in ["fundamental", "separating", "nonseparating", "value", "root_kind"]:
                row[key] = "arbitrary nonnumeric poison"
        _, groups = self.analyze(packet)
        self.assertEqual(groups, self.groups)

    def test_actual_coefficient_corruption_is_rejected(self):
        packet = copy.deepcopy(self.packet)
        packet["rows"][51]["coefficient"] = [0, 1]
        with self.assertRaisesRegex(ValueError, "actual fullClaim at 51"):
            self.analyze(packet)

    def test_original_index_loss_and_reordering_are_rejected(self):
        packet = copy.deepcopy(self.packet)
        packet["rows"].pop(0)
        with self.assertRaisesRegex(ValueError, "Original815 frame"):
            self.analyze(packet)
        packet = copy.deepcopy(self.packet)
        packet["rows"][0], packet["rows"][1] = packet["rows"][1], packet["rows"][0]
        with self.assertRaisesRegex(ValueError, "Original815 frame"):
            self.analyze(packet)

    def test_classification_metadata_is_checked(self):
        for field, value, message in [("coefficient_zero", False, "Coefficient-zero flag"),
                                       ("genus_guard", False, "genus guard"),
                                       ("evaluated", 0, "Non-boolean")]:
            packet = copy.deepcopy(self.packet)
            packet["rows"][0][field] = value
            with self.assertRaisesRegex(ValueError, message):
                self.analyze(packet)

    def test_query_conventions_are_checked(self):
        packet = copy.deepcopy(self.packet)
        packet["query"]["source_curve"] = [1, 0]
        with self.assertRaisesRegex(ValueError, "Original F1 query"):
            self.analyze(packet)

    def test_module_bound_and_zero_reason_are_checked(self):
        with self.assertRaisesRegex(ValueError, "1–25"):
            exporter.module_text("Bad", "coefficient_zero", list(range(26)), self.records)
        with self.assertRaisesRegex(ValueError, "Nonzero source"):
            exporter.module_text("Bad", "coefficient_zero", [51], self.records)
        with self.assertRaisesRegex(ValueError, "Zero source"):
            exporter.module_text("Bad", "nonzero_coefficient_genus_guard", [0], self.records)

    def test_guard_proof_mentions_actual_source_not_native_maximum(self):
        text, audits, rows = exporter.module_text(
            "Guard", "nonzero_coefficient_genus_guard", [51], self.records)
        self.assertIn("2 ≤ (L24Gluing.term 51).expression.maxComponentGenus", text)
        self.assertIn("L24CorrectionsReplay.fullClaim 51 ≠ 0", text)
        self.assertIn("originalWeighted_eq_zero_of_genus_guard 51 genusGuard51", text)
        self.assertEqual(text.count("decide +kernel"), 2)
        self.assertEqual(len(audits), 3)
        self.assertEqual(rows[0]["actual_coefficient"], [1, 3])

    def test_helper_pin_checked_before_helper_execution_or_output(self):
        with tempfile.TemporaryDirectory() as d:
            helper = Path(d) / "poison.py"
            marker = Path(d) / "executed"
            helper.write_text("from pathlib import Path\nPath(" + repr(str(marker)) + ").touch()\n")
            output = Path(d) / "out"
            with self.assertRaisesRegex(ValueError, "pin mismatch before helper execution"):
                self.generate(output, helper=helper)
            self.assertFalse(marker.exists())
            self.assertFalse(output.exists())

    def test_all_source_pins_and_packet_pin_checked_before_output(self):
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d) / "repo"
            for relative in [exporter.SOURCE, exporter.CLAIMS, exporter.ASSEMBLY]:
                target = repo / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(args.repository / relative, target)
            for relative in [exporter.SOURCE, exporter.CLAIMS, exporter.ASSEMBLY]:
                target = repo / relative
                saved = target.read_bytes()
                target.write_bytes(saved + b"\n-- corrupted source\n")
                output = Path(d) / "out"
                with self.assertRaisesRegex(ValueError, "pin mismatch before helper execution"):
                    self.generate(output, repository=repo)
                self.assertFalse(output.exists())
                target.write_bytes(saved)
            packet = Path(d) / "packet.json"
            packet.write_bytes(args.packet.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "pin mismatch before helper execution"):
                self.generate(Path(d) / "out", packet=packet)
            self.assertFalse((Path(d) / "out").exists())

    def test_portable_repeat_and_all_actual_source_obligations(self):
        with tempfile.TemporaryDirectory() as d:
            one = self.generate(Path(d) / "one")
            two = self.generate(Path(d) / "two")
            self.assertEqual(one["audit_count"], 269)
            self.assertEqual(len(one["modules"]), 6)
            obligations, audits = [], []
            for a, b in zip(one["modules"], two["modules"]):
                self.assertEqual(a["sha256"], b["sha256"])
                self.assertEqual(Path(a["source"]).read_bytes(), Path(b["source"]).read_bytes())
                self.assertLessEqual(len(a["rows"]), 25)
                obligations.extend(row["original_index"] for row in a["rows"])
                audits.extend(a["audit_names"])
                for row in a["rows"]:
                    text = Path(a["source"]).read_text()
                    self.assertIn("originalWeighted " + str(row["original_index"]) + " = 0", text)
            self.assertEqual(sorted(obligations), list(range(121)))
            self.assertEqual(len(set(audits)), 269)
            self.assertEqual(one["coverage_sha256"], two["coverage_sha256"])
            self.assertEqual(one["audit_sha256"], two["audit_sha256"])
            self.assertFalse(one["acceptance_plan"]["lean_jobs_run"])
            self.assertFalse(one["native_values_read_or_assumed"])


if __name__ == "__main__":
    unittest.main(argv=["test_f1_root_zero_rows.py"] + unittest_args)
