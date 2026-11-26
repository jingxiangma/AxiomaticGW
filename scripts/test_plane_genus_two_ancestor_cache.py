"""Full-key, dependency and actual kernel checks for shared ancestor certificates."""
import copy
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_plane_genus_two_ancestor_cache import PREFIX, key, psi, read_report, sources
from gkm_plane_few_markings import compare_candidates

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "environments/genus-two-plane-ancestor-cache-candidate.json"
FIXTURES = ROOT / "AxiomaticGW/GKM/Fixtures"


def coherent_wrong_terminal(report):
    """Forge a low-psi value and propagate it consistently through all candidate equations."""
    result = copy.deepcopy(report)
    values = {}

    def evaluate(terms):
        total = Fraction(0)
        for term in terms:
            product = Fraction(*term["coefficient"])
            for code in term["monomial"]:
                product *= values[key(code)]
            total += product
        return total

    for i, row in enumerate(result["ancestor_rows"]):
        q = key(row["key"])
        value = (Fraction(0) if i == 2 else Fraction(*row["value"])) if psi(q) <= 1 else evaluate(row["terms"])
        row["value"] = [value.numerator, value.denominator]
        values[q] = value
    for row in result["requests"]:
        value = evaluate(row["terms"])
        row["value"] = [value.numerator, value.denominator]
    return result


class AncestorCache(unittest.TestCase):
    def test_complete_regeneration_and_equation_coverage(self):
        raw = REPORT.read_bytes()
        report = read_report(raw)
        self.assertEqual(len(report["ancestor_rows"]), 39)
        self.assertEqual(sum(len(r["terms"]) for r in report["ancestor_rows"]), 539)
        self.assertEqual(sum(len(t["monomial"]) for r in report["ancestor_rows"]
                             for t in r["terms"]), 5)
        generated = sources(raw)
        for name, text in generated.items():
            self.assertEqual((FIXTURES / name).read_text(), text, name)
        arithmetic = "\n".join(v for k, v in generated.items()
                               if k not in (PREFIX + "Data.lean", PREFIX + "Replay.lean"))
        for i, row in enumerate(report["ancestor_rows"]):
            name = f"terminal_{i}" if psi(key(row["key"])) <= 1 else f"reduction_{i}"
            self.assertEqual(arithmetic.count("theorem " + name + " :"), 1)
            self.assertIn(f"exact row_{i}", generated[PREFIX + "Replay.lean"])

    def test_all_descendants_match_gkm(self):
        report = read_report(REPORT.read_bytes())
        names = ["unit", "H", "pt"]
        candidate = {"schema_version": 1, "kind": "axiomatic_gw.plane_genus_two_few_markings",
                     "positive_energy_bound": 4, "maximum_markings": 2, "cases": []}
        for row in report["requests"]:
            q = row["query"]
            candidate["cases"].append({"target": "X0", "genus": q["genus"],
                                       "class": q["curve"],
                                       "powers": [k for _, k in q["insertions"]],
                                       "labels": [names[a] for a, _ in q["insertions"]],
                                       "ordinary": row["value"]})
        self.assertEqual(compare_candidates(json.dumps(candidate),
                         (ROOT / "environments/gkm-plane-genus-two-few-markings.json").read_bytes()), 48)

    def test_malformed_or_unbound_data_rejected(self):
        original = json.loads(REPORT.read_bytes())
        mutations = [
            lambda r: r.update(schema_version=True),
            lambda r: r.update(proof_status="proved"),
            lambda r: r["ancestor_rows"][2]["key"].__setitem__(0, 1),
            lambda r: r["ancestor_rows"][2]["key"].__setitem__(1, 2),
            lambda r: r["ancestor_rows"][2]["key"].__setitem__(2, 3),
            lambda r: r["ancestor_rows"][2]["key"].__setitem__(3, -1),
            lambda r: r["ancestor_rows"][6]["value"].__setitem__(1, 0),
            lambda r: r["ancestor_rows"].append(copy.deepcopy(r["ancestor_rows"][0])),
            lambda r: r["ancestor_rows"].pop(2),
            lambda r: r["ancestor_rows"][7]["terms"][0].update(monomial=[r["ancestor_rows"][7]["key"]]),
            lambda r: r["ancestor_rows"][6]["terms"][0].update(coefficient=[1, 1]),
            lambda r: r["ancestor_rows"][6].update(value=[1, 1]),
            lambda r: r["requests"].pop(),
            lambda r: r["requests"][0]["query"].update(curve=[0]),
            lambda r: r["requests"][0]["query"].update(insertions=[[1, 4]]),
            lambda r: r["requests"][0]["query"].update(genus=True),
            lambda r: r["requests"][0].update(value=[1, 1]),
        ]
        for i, mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                changed = copy.deepcopy(original)
                mutate(changed)
                with self.assertRaises(ValueError):
                    read_report(json.dumps(changed))
        with self.assertRaises(ValueError):
            read_report('{"schema_version":1,"schema_version":1}')

    def test_actual_kernel_rejects_coherent_wrong_terminal(self):
        original = json.loads(REPORT.read_bytes())
        for expected, report in [(True, original), (False, coherent_wrong_terminal(original))]:
            with self.subTest(accepted=expected), tempfile.TemporaryDirectory() as directory:
                raw = json.dumps(report).encode()
                # Serialization, dependency closure and all candidate arithmetic still pass.
                read_report(raw)
                source = sources(raw)[PREFIX + "Data.lean"]
                source += "\nnamespace AxiomaticGW.GKM.PlaneGenusTwoAncestors\n"
                source += "open BelorousskiPandharipande\n"
                source += "example : value 2 = planeLowPsiValueWith GenusTwoPlaneLine.values (key 2) := by cbv\n"
                source += "end AxiomaticGW.GKM.PlaneGenusTwoAncestors\n"
                path = Path(directory) / "IncomingAncestor.lean"
                path.write_text(source)
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        capture_output=True, text=True)
                if expected:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("error", result.stdout + result.stderr)

    def test_actual_kernel_rejects_value_preserving_comparison_forgery(self):
        original = json.loads(REPORT.read_bytes())
        changed_coefficient = copy.deepcopy(original)
        changed_coefficient["requests"][0]["terms"][-1]["coefficient"] = [7, 1]
        missing_zero_term = copy.deepcopy(original)
        missing_zero_term["requests"][0]["terms"].pop()
        changed_zero_key = copy.deepcopy(original)
        changed_zero_key["requests"][0]["terms"][-1]["monomial"] = [
            original["ancestor_rows"][1]["key"]]
        for name, report in [("valid", original), ("coefficient", changed_coefficient),
                             ("omission", missing_zero_term), ("full_key", changed_zero_key)]:
            with self.subTest(case=name), tempfile.TemporaryDirectory() as directory:
                raw = json.dumps(report).encode()
                # All mutations preserve the candidate value because the changed term is zero.
                read_report(raw)
                source = sources(raw)[PREFIX + "Descendants.lean"]
                source = source.split("private theorem cached_0 :", 1)[0]
                source += "\nend AxiomaticGW.GKM.PlaneGenusTwoAncestors\n"
                path = Path(directory) / "IncomingComparison.lean"
                path.write_text(source)
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        capture_output=True, text=True)
                if name == "valid":
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("error", result.stdout + result.stderr)

    def test_actual_kernel_rejects_value_preserving_boundary_forgery(self):
        original = json.loads(REPORT.read_bytes())
        changed = copy.deepcopy(original)
        terms = changed["ancestor_rows"][12]["terms"]
        # The two changed constants cancel numerically, but neither is the
        # original signed boundary term. Full equation replay must notice.
        for term, delta in zip(terms[:2], (1, -1)):
            self.assertEqual(term["monomial"], [])
            value = Fraction(*term["coefficient"]) + delta
            term["coefficient"] = [value.numerator, value.denominator]
        for accepted, report in [(True, original), (False, changed)]:
            with self.subTest(accepted=accepted), tempfile.TemporaryDirectory() as directory:
                raw = json.dumps(report).encode()
                read_report(raw)
                data = sources(raw)[PREFIX + "Data.lean"]
                incoming = data.split("def terms_12 :", 1)[1].split("\n/--", 1)[0]
                source = (
                    "import AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointAncestor\n"
                    "open AxiomaticGW AxiomaticGW.SurfaceGenusTwo AxiomaticGW.GKM\n"
                    "open PlaneGenusTwoAncestors\n"
                    "def incomingTerms :" + incoming + "\n"
                    "example : ancestorReductionTerms (key 12) (by decide +kernel) =\n"
                    "    incomingTerms := by\n"
                    "  rw [PlaneGenusTwoPointAncestor.reduction]\n"
                    "  decide +kernel\n")
                path = Path(directory) / "IncomingBoundary.lean"
                path.write_text(source)
                result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                        capture_output=True, text=True)
                if accepted:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("false", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
