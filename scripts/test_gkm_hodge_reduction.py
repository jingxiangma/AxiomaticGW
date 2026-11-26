"""Verify reduced Hodge vertex certificates, including a kernel rejection at a fixed signature."""
import json
from pathlib import Path
import tempfile
import unittest

from gkm_hodge_reduction import reduction
from gkm_hodge_vertex_certificate import emit, rows
from gkm_research_query import incoming_claim
from gw_query import ROOT, checked_axioms, replay_lean


class HodgeVertexReplay(unittest.TestCase):
    def test_held_vertices(self):
        for name, count in (("exceptional-pair", 12), ("double-ruling", 139)):
            path = ROOT / f"environments/gkm-hodge-reduction-{name}.json"
            raw = path.read_bytes()
            data = json.loads(raw)
            values = rows(data["vertices"])
            self.assertEqual(len(values), count)
            computed = reduction(rows(data["seeds"]))
            self.assertTrue(all(computed(ls, psis) == v for (ls, psis), v in values.items()))
            self.assertEqual(emit(raw), path.with_suffix(".lean").read_text())
            run = replay_lean(path.with_suffix(".lean"))
            self.assertEqual(run.returncode, 0, run.stdout)
            checked_axioms(run.stdout, "AxiomaticGW.GKM.HodgeVertexCertificate.vertex_sound")
            with self.assertRaisesRegex(ValueError, "Unsupported GKM descendant report kind"):
                incoming_claim(data["query"], raw)

    def test_missing_seed_and_wrong_claim(self):
        path = ROOT / "environments/gkm-hodge-reduction-exceptional-pair.json"
        data = json.loads(path.read_bytes())
        with self.assertRaisesRegex(ValueError, "all eight"):
            emit(json.dumps(dict(data, seeds=data["seeds"][:-1])).encode())
        query = dict(data["query"], **{"class": [0, 1, 0]})
        with self.assertRaisesRegex(ValueError, "Changed request"):
            emit(json.dumps(dict(data, query=query)).encode())

    def test_importable_cubic_vertices(self):
        path = ROOT / "environments/gkm-hodge-reduction-exceptional-cubic.json"
        raw = path.read_bytes()
        data = json.loads(raw)
        self.assertEqual(len(rows(data["vertices"])), 10)
        fixture = ROOT / "AxiomaticGW/GKM/Fixtures/ExceptionalGenusTwoVertexValues.lean"
        self.assertEqual(emit(raw, exceptional_cubic=True), fixture.read_text())
        with self.assertRaisesRegex(ValueError, "original ordered request|Changed request"):
            query = dict(data["query"], **{"class": [0, 1, 0]})
            emit(json.dumps(dict(data, query=query)).encode(), exceptional_cubic=True)

    def test_incorrect_vertex_rejected_by_lean(self):
        path = ROOT / "environments/gkm-hodge-reduction-exceptional-pair.json"
        data = json.loads(path.read_bytes())
        data["vertices"][0]["value"] = [0, 1]
        with tempfile.TemporaryDirectory() as temp:
            changed = Path(temp) / "Changed.lean"
            changed.write_text(emit(json.dumps(data).encode()))
            run = replay_lean(changed)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("vertices.all agrees = true", run.stdout)


if __name__ == "__main__":
    unittest.main()
