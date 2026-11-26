"""Exercise the query CLI, its geometric domain and its exported Lean claims."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from gw_query import (ROOT, canonical_family, checked_axioms, reconstruct, replay_lean,
                      save_certificate, select, validate)
from gkm_research_query import incoming_claim, specialization_source


class ResearchQuery(unittest.TestCase):
    def test_domain_and_basis(self):
        base = {"genus": 0, "target": "X2", "class": [1, 0, 0], "insertions": []}
        request, _, energy = validate(base)
        self.assertEqual((request, energy), (base, 1))
        bad = [{"class": [0, 0, 0]}, {"class": [1]}, {"genus": True}, {"genus": 3},
               {"class": [1, 0, 0.5]}, {"insertions": [["E3", 0]]}, {"insertions": [["H", -1]]},
               {"target": "X9"}, {"genus": 1, "class": [0, 0, 0]}, {"claim": 1}]
        for change in bad:
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate({**base, **change})

    def test_order_and_audit(self):
        self.assertEqual(canonical_family([["E2", 1], ["pt", 0]], 1), ".exceptional 1")
        self.assertIsNone(canonical_family([["pt", 0], ["E2", 1]], 1))
        self.assertEqual(checked_axioms("'T' does not depend on any axioms", "T"), [])
        with self.assertRaises(ValueError):
            checked_axioms("'T' depends on axioms: [propext, extra]", "T")
        with self.assertRaises(ValueError):
            checked_axioms("'S' depends on axioms: [propext]", "T")

    def test_cli_and_replay(self):
        query = {"target": "X1", "genus": 1, "class": [1, 0],
                 "insertions": [["E1", 1], ["E1", 0], ["E1", 0]]}
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            request, certificate = directory / "request.json", directory / "Proof.lean"
            request.write_text(json.dumps(query))
            cli = [sys.executable, "-B", str(ROOT / "scripts/gw_query.py"), str(request),
                   "--certificate", str(certificate)]
            result = subprocess.run(cli, check=True, capture_output=True, text=True)
            report = json.loads(result.stdout)
            source = certificate.read_bytes()
            self.assertEqual(report["query"], query)
            self.assertEqual(report["ordinary_rational"], [1, 12])
            self.assertEqual(report["certificate_sha256"], hashlib.sha256(source).hexdigest())
            self.assertIn(report["theorem"], report["axioms"])
            self.assertIn(report["geometric_theorem"], report["axioms"])
            shown = directory / "GeometricType.lean"
            shown.write_bytes(source + f"\n#print sig {report['geometric_theorem']}\n".encode())
            shown_result = replay_lean(shown)
            self.assertEqual(shown_result.returncode, 0, shown_result.stdout)
            self.assertRegex(" ".join(shown_result.stdout.split()),
                             r"SurfaceQuery\.checkedEval U [\w.]*request = some \(1 / 12\)")
            replay_lean(certificate).check_returncode()
            second = subprocess.run(cli, capture_output=True, text=True)
            self.assertIn("already exists", second.stderr)
            self.assertEqual(certificate.read_bytes(), source)
            with self.assertRaises(FileExistsError):
                save_certificate(certificate, "different")
            changed = source.replace(b"some (1 / 12", b"some (1 / 13")
            self.assertNotEqual(changed, source)
            certificate.write_bytes(changed)
            negative = replay_lean(certificate)
            self.assertNotEqual(negative.returncode, 0)
            self.assertIn("false", negative.stdout.lower())

    def test_auxiliary_class_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            request, output = directory / "input.json", directory / "Result.lean"
            request.write_text('{"target":"X2","genus":0,"class":[0,0,0],"insertions":[]}')
            run = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/gw_query.py"),
                                  str(request), "--certificate", str(output)], capture_output=True)
            self.assertEqual(json.loads(run.stderr)["status"], "unverified")
            self.assertFalse(output.exists())

    def test_nonzero_exceptional_descendant(self):
        query = {"target": "X2", "genus": 2, "class": [0, 1, 0], "insertions": [["E2", 2]]}
        report, _ = reconstruct(query, gkm_report=ROOT / "environments/gkm-genus-two-one-marking.json")
        self.assertEqual(report["ordinary_rational"], [-1, 240])
        self.assertIn("GenusTwoOneMarkingReplay", report["module"])
        self.assertIn("genusTwoExceptional E2", report["geometric_seed_hypotheses"])
        self.assertIn(report["comparison_theorem"], report["axioms"])

    def test_strict_line_dilaton(self):
        query = {"target": "X2", "genus": 2, "class": [0, 0, 1],
                 "insertions": [["H", 2], ["unit", 1]]}
        report, _ = reconstruct(query, gkm_report=ROOT / "environments/gkm-genus-two-unit-pairs.json")
        self.assertEqual(report["ordinary_rational"], [1, 80])
        self.assertIn("UnitPairReplay", report["module"])
        self.assertIn(report["geometric_interpretation"], report["axioms"])

    def test_divisor_reconstruction(self):
        report = ROOT / "environments/gkm-genus-two-divisor-pairs.json"
        plane = {"target": "X0", "genus": 2, "class": [1], "insertions": [["H", 0], ["H", 4]]}
        result, _ = reconstruct(plane, gkm_report=report)
        self.assertEqual(result["ordinary_rational"], [-1, 192])
        self.assertNotIn("equivariant_comparison_theorem", result)
        blowup = {"target": "X1", "genus": 2, "class": [1, 0],
                  "insertions": [["E1", 0], ["E1", 2]]}
        result, _ = reconstruct(blowup, gkm_report=report)
        self.assertEqual(result["ordinary_rational"], [1, 240])
        self.assertIn("DivisorPairReplay", result["module"])
        self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])

    def test_ordered_pair_dispatch(self):
        counts = {}
        for name in ("unit", "divisor"):
            cases = json.loads((ROOT / f"environments/gkm-genus-two-{name}-pairs.json").read_bytes())["cases"]
            for case in cases:
                marks = [list(m) for m in zip(case["labels"], case["powers"])]
                q, surface, energy = validate({"target": case["target"], "class": case["class"],
                                               "genus": 2, "insertions": marks})
                route = select(q, surface, energy)
                if ("PairReplay" in route.module or "BlowupTwoLineCompletedReplay" in route.module
                        or "PlaneGenusTwoFewMarkingBenchmarks" in route.module):
                    counts[name] = counts.get(name, 0) + 1
            self.assertEqual(counts[name], {"unit": 76, "divisor": 112}[name])

    def test_strict_line_absolute_values(self):
        base = {"target": "X2", "genus": 2, "class": [0, 0, 1]}
        for marks, frame, expected in (
                ([["pt", 0], ["pt", 0]], "bl2-line-canonical", [0, 1]),
                ([["pt", 1]], "bl2-line-one-marking", [0, 1]),
                ([["unit", 0], ["pt", 2]], "genus-two-unit-pairs", [0, 1]),
                ([["H", 0], ["H", 2]], "genus-two-divisor-pairs", [1, 240])):
            with self.subTest(marks=marks):
                result, _ = reconstruct(dict(base, insertions=marks),
                                        gkm_report=ROOT / f"environments/gkm-{frame}.json")
                self.assertEqual(result["ordinary_rational"], expected)

    def test_complete_energy_one_values(self):
        report = ROOT / "environments/gkm-genus-two-energy-one.json"
        for target, beta, marks, expected in (
                ("X1", [1, 0], [["E1", 1], ["E1", 1]], [1, 144]),
                ("X1", [1, 0], [["unit", 2], ["E1", 1]], [-5, 288]),
                ("X2", [0, 1, 0], [["unit", 2], ["E1", 1]], [0, 1]),
                ("X2", [0, 0, 1], [["pt", 0], ["H", 1]], [0, 1])):
            with self.subTest(marks=marks):
                result, _ = reconstruct({"target": target, "genus": 2, "class": beta, "insertions": marks},
                                        gkm_report=report)
                self.assertEqual(result["ordinary_rational"], expected)
                self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_full_field_research_report_and_equivalent_fraction(self):
        query = {"target": "X1", "genus": 2, "class": [1, 0],
                 "insertions": [["E1", 1], ["E1", 1]]}
        report = json.loads((ROOT / "environments/gkm-genus-two-energy-one.json").read_bytes())
        row = next(c for c in report["cases"] if c["target"] == "X1" and
                   c["labels"] == ["E1", "E1"] and c["powers"] == [1, 1])
        # A fresh single-query report with a different regular representative of 1/144.
        report["kind"] = "gkm_localization.surface_research_query"
        report["cases"] = [row]
        row["equivariant"] = {"numerator": [[[0, 0], [1, 1]], [[0, 1], [1, 1]], [[1, 0], [1, 1]]],
                              "denominator": [[[0, 0], [144, 1]], [[0, 1], [144, 1]], [[1, 0], [144, 1]]]}
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "research.json"
            path.write_text(json.dumps(report))
            result, _ = reconstruct(query, gkm_report=path)
            self.assertEqual(result["ordinary_rational"], [1, 144])
            self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
            self.assertEqual(result["gkm_comparison"]["energy_one_row"]["target"], "X1")
            # (1+2x+y)/(144+144x+144y) has the same ordinary value and different torus dependence.
            row["equivariant"]["numerator"][2][1] = [2, 1]
            path.write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(query, gkm_report=path)

    def test_gkm_binding(self):
        query = {"target": "X1", "genus": 1, "class": [1, 0],
                 "insertions": [["E1", 1], ["E1", 0], ["E1", 0]]}
        raw = (ROOT / "environments/gkm-research-f1-elliptic-exceptional.json").read_bytes()
        moved = dict(query, insertions=[["E1", 0], ["E1", 1], ["E1", 0]])
        with self.assertRaises(ValueError):
            incoming_claim(moved, raw)
        report = json.loads(raw)
        row = report["cases"][0]
        row["equivariant"] = {"numerator": [[[0, 0], [1, 1]], [[1, 0], [1, 1]]],
                              "denominator": [[[0, 0], [12, 1]], [[0, 1], [1, 1]]]}
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "genus-one.json"
            path.write_text(json.dumps(report))
            result, _ = reconstruct(query, gkm_report=path)
            self.assertEqual(result["ordinary_rational"], [1, 12])
            self.assertIn(result["comparison_theorem"], result["axioms"])
            self.assertNotIn("equivariant_comparison_theorem", result)
            row["ordinary"] = [0, 1]
            row["equivariant"]["numerator"] = []
            path.write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, "reconstruction returned 1/12"):
                reconstruct(query, gkm_report=path)

    def test_held_descendant_reports(self):
        names = ("three-point-descendants", "genus-zero-descendants", "genus-one-descendants",
                 "genus-two-degree-zero", "plane-genus-two-few-markings", "f1-fiber-h",
                 "f1-fiber-remaining", "genus-two-one-marking", "bl2-line-one-marking",
                 "bl2-line-canonical", "genus-two-unit-pairs", "genus-two-divisor-pairs",
                 "genus-two-positive-pairs", "genus-two-energy-one", "bl2-line-point-unit-square",
                 "f1-plane-line", "f1-fiber-one-marking", "f1-fiber-pairs",
                 "f1-double-exceptional-one-marking", "f1-double-exceptional-pairs", "bl2-mixed-exceptional")
        for name in names:
            with self.subTest(name=name):
                raw = (ROOT / f"environments/gkm-{name}.json").read_bytes()
                sample = json.loads(raw)["cases"][0]
                query = {"target": sample["target"], "genus": sample["genus"], "class": sample["class"],
                         "insertions": list(map(list, zip(sample["labels"], sample["powers"])))}
                self.assertEqual(incoming_claim(query, raw)["equivariant"], sample["equivariant"])
                with self.assertRaisesRegex(ValueError, "no unique row"):
                    incoming_claim(dict(query, genus=(query["genus"] + 1) % 3), raw)

    def test_f1_energy_three_canonical_table(self):
        packet = ROOT / "environments/gkm-f1-plane-line.json"
        for row in json.loads(packet.read_bytes())["cases"]:
            marks = [list(m) for m in zip(row["labels"], row["powers"])]
            query = {"target": "X1", "genus": 2, "class": [1, 1], "insertions": marks}
            with self.subTest(marks=marks):
                result, _ = reconstruct(query, gkm_report=packet)
                self.assertEqual(result["ordinary_rational"], [0, 1])
                self.assertIn("F1PlaneLineL24Replay", result["module"])
                self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_f1_fiber_singletons(self):
        packet = ROOT / "environments/gkm-f1-fiber-one-marking.json"
        for label, power, expected in (("unit", 4, [-1, 120]), ("H", 3, [-7, 960]),
                                       ("E1", 3, [-23, 2880]), ("pt", 2, [1, 240])):
            query = {"target": "X1", "genus": 2, "class": [0, 1], "insertions": [[label, power]]}
            with self.subTest(label=label):
                result, _ = reconstruct(query, gkm_report=packet)
                self.assertEqual(result["ordinary_rational"], expected)
                self.assertIn(result["geometric_theorem"], result["axioms"])
                self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])

    def test_energy_two_held_frames(self):
        from gkm_f1_energy_two import DOUBLE_PAIRS, DOUBLE_SINGLETONS, FIBER_PAIRS
        for module, filename, name, count in (
                (FIBER_PAIRS, "f1-fiber-pairs", "F1FiberPairs", 64),
                (DOUBLE_SINGLETONS, "f1-double-exceptional-one-marking", "F1DoubleExceptionalOneMarking", 4),
                (DOUBLE_PAIRS, "f1-double-exceptional-pairs", "F1DoubleExceptionalPairs", 64)):
            with self.subTest(frame=filename):
                raw = (ROOT / f"environments/gkm-{filename}.json").read_bytes()
                source = module.emit(raw)
                self.assertEqual(source, (ROOT / f"AxiomaticGW/GKM/Fixtures/{name}.lean").read_text())
                data = json.loads(raw)
                self.assertEqual(len(data["cases"]), count)
                data["cases"].reverse()
                self.assertEqual(source.split("-/", 1)[1],
                                 module.emit(json.dumps(data).encode()).split("-/", 1)[1])
                data["cases"][0]["class"] = [2, 0] if module is FIBER_PAIRS else [0, 1]
                with self.assertRaisesRegex(ValueError, "Changed request"):
                    module.emit(json.dumps(data).encode())

    def test_energy_two_classes_and_fiber_pairs(self):
        # The class is essential even for identical genus, power, insertion and energy.
        tests = [
            ([0, 1], [["E1", 3]], "f1-fiber-one-marking", [-23, 2880]),
            ([2, 0], [["E1", 3]], "f1-double-exceptional-one-marking", [3, 320]),
            ([0, 1], [["unit", 3], ["E1", 1]], "f1-fiber-pairs", [-113, 2880]),
            ([2, 0], [["unit", 3], ["E1", 1]], "f1-double-exceptional-pairs", [37, 1920]),
            ([0, 1], [["E1", 0], ["E1", 3]], "f1-fiber-pairs", [-7, 576]),
        ]
        for beta, insertions, frame, expected in tests:
            query = {"target": "X1", "genus": 2, "class": beta, "insertions": insertions}
            with self.subTest(query=query):
                result, theorem = reconstruct(query, gkm_report=ROOT / f"environments/gkm-{frame}.json")
                self.assertEqual(result["ordinary_rational"], expected)
                self.assertIn(result["geometric_theorem"], result["axioms"])
                self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
                if frame == "f1-fiber-pairs" and insertions == [["unit", 3], ["E1", 1]]:
                    self.assertEqual(theorem, (ROOT / "environments/gkm-research-f1-fiber-pair.lean").read_text())

    def test_double_exceptional_rejects_changed_torus_dependence(self):
        raw = (ROOT / "environments/gkm-f1-double-exceptional-one-marking.json").read_bytes()
        data = json.loads(raw)
        case = next(c for c in data["cases"] if c["labels"] == ["E1"])
        # The added x vanishes at zero weights and changes the full equivariant result.
        case["equivariant"]["numerator"].append([[1, 0], [1, 1]])
        query = {"target": "X1", "genus": 2, "class": [2, 0], "insertions": [["E1", 3]]}
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "changed.json"
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(query, gkm_report=path)

    def test_dimension_vanishing_and_divisor_pair(self):
        cases = [
            ({"target": "X0", "genus": 0, "class": [5], "insertions": []}, "SurfaceQuery.dimensionVanishing?_sound"),
            ({"target": "X1", "genus": 2, "class": [1, 1], "insertions": [["H", 4], ["E1", 0]]},
             "SurfaceGenusTwo.zeroDivisorPair?_checkedEval"),
            ({"target": "X2", "genus": 2, "class": [0, 1, 1], "insertions": [["E2", 0], ["H", 3]]},
             "SurfaceGenusTwo.zeroDivisorPair?_checkedEval"),
        ]
        for query, law in cases:
            with self.subTest(query=query):
                report_name = {"X1": "f1", "X2": "bl2-partial"}.get(query["target"])
                packet = ROOT / f"environments/gkm-zero-divisor-{report_name}.json" if report_name else None
                result, _ = reconstruct(query, gkm_report=packet)
                if packet:
                    self.assertEqual(result["gkm_comparison"]["zero_divisor_row"]["target"], query["target"])
                    self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
                self.assertEqual(result["ordinary_rational"], [0, 1])
                self.assertEqual(result["geometric_seed_hypotheses"], {})
                self.assertEqual(result["geometric_interpretation"], f"AxiomaticGW.{law}")
                self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_exceptional_marked_graph_comparison(self):
        packet = ROOT / "environments/gkm-genus-two-energy-one.json"
        for surface, beta, label, power in (("X1", [1, 0], "pt", 1), ("X2", [1, 0, 0], "E2", 2)):
            q = {"target": surface, "genus": 2, "class": beta, "insertions": [[label, power]]}
            with self.subTest(q=q):
                result, _ = reconstruct(q, gkm_report=packet)
                self.assertEqual(result["ordinary_rational"], [0, 1])
                self.assertIn(result["insertion_comparison_theorem"], result["axioms"])

    def test_removable_presentation_of_plane_line(self):
        packet = ROOT / "environments/gkm-research-plane-line-point-square.json"
        data = json.loads(packet.read_bytes())
        row, = data["cases"]
        # The actual two-flag answer before canceling x is (2xy - x²)/x.
        raw = {"numerator": [[[1, 1], [2, 1]], [[2, 0], [-1, 1]]],
               "denominator": [[[1, 0], [1, 1]]]}
        row["equivariant"] = raw
        q = {"target": "X0", "genus": 0, "class": [1], "insertions": [["pt", 2]]}
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "Removable.json"
            path.write_text(json.dumps(data))
            result, _ = reconstruct(q, gkm_report=path)
            self.assertEqual(result["gkm_comparison"]["equivariant"], raw)
            self.assertIn(result["submitted_presentation_theorem"], result["axioms"])
            self.assertIn(result["fixed_locus_comparison_theorem"], result["axioms"])
        row["equivariant"]["numerator"] = [[[0, 1], [1, 1]]]
        with self.assertRaisesRegex(ValueError, "needs a regular_representative"):
            incoming_claim(q, json.dumps(data).encode())

    def test_removable_regular_rational(self):
        data = json.loads((ROOT / "environments/gkm-research-f1-elliptic-exceptional.json").read_bytes())
        row, = data["cases"]
        # x(1+x)/[x(12+y)] needs an actual regular rational witness.
        row["equivariant"] = {"numerator": [[[1, 0], [1, 1]], [[2, 0], [1, 1]]],
                              "denominator": [[[1, 0], [12, 1]], [[1, 1], [1, 1]]]}
        row["regular_representative"] = {"numerator": [[[0, 0], [1, 1]], [[1, 0], [1, 1]]],
                                         "denominator": [[[0, 0], [12, 1]], [[0, 1], [1, 1]]]}
        q = {"target": "X1", "genus": 1, "class": [1, 0], "insertions": [["E1", 1], ["E1", 0], ["E1", 0]]}
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "Rational.json"
            path.write_text(json.dumps(data))
            result, _ = reconstruct(q, gkm_report=path)
            self.assertIn(result["submitted_presentation_theorem"], result["axioms"])
            self.assertEqual(result["ordinary_rational"], [1, 12])
        row["regular_representative"]["numerator"][1][1] = [2, 1]
        with self.assertRaisesRegex(ValueError, "Invalid regular representative"):
            incoming_claim(q, json.dumps(data).encode())

    def test_plane_line_point_nonconstant_full_field(self):
        query = {"target": "X0", "genus": 0, "class": [1], "insertions": [["pt", 2]]}
        packet = ROOT / "environments/gkm-research-plane-line-point-square.json"
        result, proof = reconstruct(query, gkm_report=packet)
        self.assertEqual(proof, packet.with_suffix(".lean").read_text())
        self.assertEqual(result["ordinary_rational"], [0, 1])
        self.assertEqual(result["gkm_comparison"]["plane_line_point_power"], 2)
        self.assertIn(result["equivariant_grading_theorem"], result["axioms"])
        self.assertIn(result["fixed_locus_comparison_theorem"], result["axioms"])
        self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
        data = json.loads(packet.read_bytes())
        next(t for t in data["cases"][0]["equivariant"]["numerator"] if t[0] == [0, 1])[1] = [3, 1]
        with tempfile.TemporaryDirectory() as folder:
            changed = Path(folder) / "changed.json"
            changed.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(query, gkm_report=changed)

    def test_genus_two_exceptional_cubics(self):
        cases = (("X1", [1, 0], "E1", "f1", "f1"), ("X2", [1, 0, 0], "E1", "bl2", "first"),
                 ("X2", [0, 1, 0], "E2", "bl2-second", "second"))
        for surface, beta, label, filename, sector in cases:
            path = ROOT / f"environments/gkm-research-{filename}-exceptional-cubic.json"
            q = {"target": surface, "genus": 2, "class": beta, "insertions": [[label, 3]]}
            with self.subTest(sector=sector):
                result, proof = reconstruct(q, gkm_report=path)
                self.assertEqual(result["gkm_comparison"]["exceptional_cubic"], sector)
                self.assertIn(result["integrated_locus_comparison_theorem"], result["axioms"])
                if sector == "first":
                    self.assertEqual(proof, path.with_suffix(".lean").read_text())
                self.assertEqual(result["ordinary_rational"], [0, 1])
                self.assertEqual(result["geometric_seed_hypotheses"], {})
                self.assertIn(result["fixed_locus_comparison_theorem"], result["axioms"])
        # Both axes specialize to zero. Swapping just the field function must fail.
        second = json.loads(path.read_bytes())
        first = json.loads((ROOT / "environments/gkm-research-bl2-exceptional-cubic.json").read_bytes())
        second["cases"][0]["equivariant"] = first["cases"][0]["equivariant"]
        with tempfile.TemporaryDirectory() as folder:
            swapped = Path(folder) / "Swapped.json"
            swapped.write_text(json.dumps(second))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(q, gkm_report=swapped)

    def test_double_exceptional_cubic_reconstruction(self):
        cases = (("X1", [2, 0], "E1", "f1"), ("X2", [2, 0, 0], "E1", "bl2"),
                 ("X2", [0, 2, 0], "E2", "bl2-second"))
        for target, beta, label, name in cases:
            query = {"target": target, "genus": 2, "class": beta, "insertions": [[label, 3]]}
            path = ROOT / f"environments/gkm-research-{name}-double-exceptional-cubic.json"
            with self.subTest(surface=target, curve=beta):
                result, _ = reconstruct(query, gkm_report=path)
                self.assertEqual(result["ordinary_rational"], [3, 320])
                self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
        # A linear perturbation has the same ordinary specialization.
        data = json.loads(path.read_bytes())
        data["cases"][0]["equivariant"]["numerator"].append([[1, 0], [1, 1]])
        with tempfile.TemporaryDirectory() as folder:
            wrong = Path(folder) / "wrong.json"
            wrong.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(query, gkm_report=wrong)

    def test_double_exceptional_ordered_pairs(self):
        from gkm_bl2_double_exceptional_pairs import REQUESTS, emit
        path = ROOT / "environments/gkm-bl2-double-exceptional-pairs.json"
        source = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalPairs.lean"
        self.assertEqual(emit(path.read_bytes()), source.read_text())
        for row in (0, 3, 4, 11):
            beta, powers, labels = REQUESTS["X2"][row]
            q = {"target": "X2", "genus": 2, "class": list(beta),
                 "insertions": [[label, k] for label, k in zip(labels, powers)]}
            result, _ = reconstruct(q, gkm_report=path)
            self.assertEqual(result["gkm_comparison"]["double_exceptional_pair_row"], row)
            self.assertEqual(result["ordinary_rational"], ([3, 320], [9, 320], [-3, 160])[row % 6 // 2])
            self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])

    def test_double_exceptional_singleton_frame(self):
        from gkm_bl2_double_exceptional_singletons import REQUESTS, emit
        path = ROOT / "environments/gkm-bl2-double-exceptional-singletons.json"
        fixture = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalSingletons.lean"
        self.assertEqual(emit(path.read_bytes()), fixture.read_text())
        for row in (0, 1, 3, 9):
            beta, powers, labels = REQUESTS["X2"][row]
            q = {"target": "X2", "genus": 2, "class": list(beta),
                 "insertions": [[labels[0], powers[0]]]}
            result, _ = reconstruct(q, gkm_report=path)
            self.assertEqual(result["gkm_comparison"]["double_exceptional_singleton_row"], row)
            self.assertEqual(result["ordinary_rational"], [13, 3840] if row == 0 else [0, 1])
            self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
            if labels == ("pt",):
                self.assertEqual(result["geometric_seed_hypotheses"], {})

    def test_double_exceptional_divisor_cup_term(self):
        from gkm_bl2_double_exceptional_few_markings import emit
        path = ROOT / "environments/gkm-bl2-double-exceptional-few-markings.json"
        fixture = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoDoubleExceptionalFewMarkings.lean"
        self.assertEqual(emit(path.read_bytes()), fixture.read_text())
        q = {"target": "X2", "genus": 2, "class": [2, 0, 0], "insertions": [["E1", 0], ["unit", 4]]}
        result, proof = reconstruct(q, gkm_report=path)
        self.assertEqual(proof, (ROOT / "environments/gkm-research-bl2-double-exceptional-marked.lean").read_text())
        # The divisor intersection and cup terms both contribute to this answer.
        self.assertEqual(result["ordinary_rational"], [1, 384])
        self.assertIn(result["exceptional_surface_comparison_theorem"], result["axioms"])
        self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_double_exceptional_interior_from_target(self):
        packet = ROOT / "environments/gkm-bl2-double-exceptional-few-markings.json"
        cases = (([2, 0, 0], [["unit", 2], ["unit", 3]], [27, 1280]),
                 ([0, 2, 0], [["E2", 1], ["E2", 2]], [-7, 160]),
                 ([0, 2, 0], [["E1", 1], ["E1", 2]], [0, 1]))
        for beta, marks, expected in cases:
            query = {"target": "X2", "genus": 2, "class": beta, "insertions": marks}
            with self.subTest(curve=beta, insertions=marks):
                result, proof = reconstruct(query, gkm_report=packet)
                self.assertEqual(result["ordinary_rational"], expected)
                self.assertIn("BlowupTwoDoubleExceptionalFewMarkings.accepted", proof)
                self.assertIn(result["exceptional_surface_comparison_theorem"], result["axioms"])
                self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_double_line_singletons_and_native_binding(self):
        from gkm_bl2_positive_plane_energy_two import emit
        packet = ROOT / "environments/gkm-bl2-positive-plane-energy-two-singletons.json"
        source = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoPositivePlaneEnergyTwoSingletons.lean"
        raw = packet.read_bytes()
        self.assertEqual(emit(raw, "singletons"), source.read_text())
        q = {"target": "X2", "genus": 2, "class": [0, 0, 2], "insertions": [["E2", 3]]}
        result, proof = reconstruct(q, gkm_report=packet)
        self.assertEqual(result["ordinary_rational"], [-3, 320])
        self.assertEqual(result["gkm_comparison"]["positive_plane_row"], {"frame": "singletons", "index": 3})
        self.assertIn("BlowupTwoDoubleLineReplay.accepted", proof)
        self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
        for curve, expected in (([0, 1, 1], [1, 2880]), ([1, 0, 1], [-23, 2880])):
            self.assertEqual(incoming_claim({**q, "class": curve}, raw)["ordinary"], expected)
        with self.assertRaisesRegex(ValueError, "Incomplete or duplicate"):
            data = json.loads(raw)
            data["cases"].pop()
            emit(json.dumps(data), "singletons")
        with tempfile.TemporaryDirectory() as folder:
            changed = Path(folder) / "shifted.json"
            data = json.loads(raw)
            data["cases"][3]["equivariant"]["numerator"].append([[1, 0], [1, 1]])
            changed.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(q, gkm_report=changed)

    def test_ruling_marked_pair_and_native_binding(self):
        from gkm_bl2_positive_plane_energy_two import emit
        packet = ROOT / "environments/gkm-bl2-positive-plane-energy-two-pairs.json"
        fixture = ROOT / "AxiomaticGW/GKM/Fixtures/BlowupTwoPositivePlaneEnergyTwoPairs.lean"
        self.assertEqual(emit(packet.read_bytes(), "pairs"), fixture.read_text())
        # The zero-power divisor has nonzero intersection and a nonzero cup correction.
        q = {"target": "X2", "genus": 2, "class": [1, 0, 1], "insertions": [["unit", 4], ["E2", 0]]}
        result, proof = reconstruct(q, gkm_report=packet)
        self.assertEqual(result["ordinary_rational"], [-127, 5760])
        self.assertEqual(result["gkm_comparison"]["positive_plane_row"], {"frame": "pairs", "index": 220})
        self.assertIn("marked_accepted (j := 220)", proof)
        self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
        changed = json.loads(packet.read_bytes())
        # Interchange the two curve labels for this marking without changing the size of the frame.
        other = next(c for c in changed["cases"] if c["class"] == [0, 1, 1]
                     and c["labels"] == ["unit", "E2"] and c["powers"] == [4, 0])
        original = changed["cases"][220]
        original["class"], other["class"] = other["class"], original["class"]
        with tempfile.TemporaryDirectory() as folder:
            altered = Path(folder) / "swapped.json"
            altered.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "GKM supplied .* while reconstruction returned"):
                reconstruct(q, gkm_report=altered)

    def test_ruling_point_divisor_product(self):
        packet = ROOT / "environments/gkm-bl2-positive-plane-energy-two-pairs.json"
        q = {"target": "X2", "genus": 2, "class": [0, 1, 1], "insertions": [["pt", 1], ["E1", 1]]}
        result, proof = reconstruct(q, gkm_report=packet)
        self.assertEqual(result["ordinary_rational"], [1, 144])
        self.assertEqual(result["gkm_comparison"]["positive_plane_row"], {"frame": "pairs", "index": 193})
        self.assertIn("ruling_divisor_point_accepted (n := 193)", proof)
        self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_strict_line_point_with_divisor_descendant(self):
        packet = ROOT / "environments/gkm-bl2-positive-plane-energy-two-pairs.json"
        query = {"target": "X2", "genus": 2, "class": [0, 0, 2], "insertions": [["E2", 1], ["pt", 1]]}
        result, proof = reconstruct(query, gkm_report=packet)
        self.assertEqual(result["ordinary_rational"], [0, 1])
        self.assertEqual(result["gkm_comparison"]["positive_plane_row"], {"frame": "pairs", "index": 83})
        self.assertIn("verified_accepted (j := 83)", proof)
        self.assertIn(result["geometric_theorem"], result["axioms"])

    def test_unstable_mixed_exceptional_graph_sum(self):
        query = {"target": "X2", "genus": 0, "class": [2, 1, 0], "insertions": []}
        packet = ROOT / "environments/gkm-research-bl2-mixed-exceptional-unstable.json"
        result, _ = reconstruct(query, gkm_report=packet)
        self.assertEqual(result["ordinary_rational"], [0, 1])
        self.assertIn(result["empty_graph_comparison_theorem"], result["axioms"])
        data = json.loads(packet.read_bytes())
        data["cases"][0]["equivariant"]["numerator"] = [[[1, 0], [1, 1]]]
        with tempfile.TemporaryDirectory() as folder:
            changed = Path(folder) / "changed.json"
            changed.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(query, gkm_report=changed)

    def test_mixed_exceptional_full_query(self):
        packet = ROOT / "environments/gkm-bl2-mixed-exceptional.json"
        query = {"target": "X2", "genus": 2, "class": [1, 1, 0], "insertions": [["unit", 2], ["unit", 3]]}
        result, theorem = reconstruct(query, gkm_report=packet)
        self.assertEqual(result["ordinary_rational"], [0, 1])
        self.assertEqual(result["gkm_comparison"]["mixed_exceptional_row"], 7)
        self.assertIn(result["geometric_theorem"], result["axioms"])
        self.assertIn(result["equivariant_comparison_theorem"], result["axioms"])
        self.assertIn(result["empty_graph_comparison_theorem"], result["axioms"])
        self.assertIn("GKM.BlowupTwoMixedExceptional.accepted 7", theorem)
        data = json.loads(packet.read_bytes())
        case = next(c for c in data["cases"] if c["powers"] == [2, 3] and c["labels"] == ["unit", "unit"])
        case["equivariant"]["numerator"] = [[[1, 0], [1, 1]]]
        with tempfile.TemporaryDirectory() as folder:
            changed = Path(folder) / "changed.json"
            changed.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Lean did not certify the query"):
                reconstruct(query, gkm_report=changed)

    def test_regular_nonconstant_specialization(self):
        # (1+x)/(12+y) is regular at zero and has value 1/12.
        fraction = {"numerator": [[[0, 0], [1, 1]], [[1, 0], [1, 1]]],
                    "denominator": [[[0, 0], [12, 1]], [[0, 1], [1, 1]]]}
        header = ("import AxiomaticGW.GKM.EquivariantCoefficients\nnamespace AxiomaticGW.Research.Control\n"
                  "theorem certified : True := True.intro\n")
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Specialization.lean"
            for value in ("(1 / 12 : ℚ)", "(1 / 13 : ℚ)"):
                code = specialization_source({"equivariant": fraction}, value, "True")
                path.write_text(header + code + "end AxiomaticGW.Research.Control\n")
                run = replay_lean(path)
                if "12" in value:
                    self.assertEqual(run.returncode, 0, run.stdout)
                else:
                    self.assertNotEqual(run.returncode, 0)
                    self.assertIn("false", run.stdout.lower())


if __name__ == "__main__":
    unittest.main()
