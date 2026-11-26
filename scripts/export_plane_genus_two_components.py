#!/usr/bin/env python3
"""Export separately checked low-genus components of the plane ancestor suite.

Symbolic rows select reusable components; they are not themselves accepted
relation certificates. Every value is checked against the original algorithm,
and every final ancestor equation must still be replayed in full.
"""
import argparse
import hashlib
import json
from pathlib import Path

from check_gkm_inputs import integer, rational, require, unique_object
from export_plane_genus_two_ancestor_cache import fields

PREFIX = "PlaneGenusTwoComponents"
NAMESPACE = "AxiomaticGW.GKM." + PREFIX
POINT = "PlaneGenusTwoPointComponents"
LABELS = (".unit", ".hyperplane", ".point")
SELECTIONS = (Path(__file__).resolve().parents[1] /
              "environments/genus-two-plane-component-selections.json")


def key(code):
    require(isinstance(code, list) and len(code) >= 4 and len(code) % 2 == 0,
            "Unpaired component key")
    code = tuple(integer(x) for x in code)
    g, d = code[:2]
    pairs = tuple(zip(code[2::2], code[3::2]))
    require(g in (0, 1, 2) and d in (0, 1), "Wrong genus or full plane curve class")
    require(all(a in range(3) and 0 <= k <= 6 for a, k in pairs), "Invalid insertion")
    require(2 * g + len(pairs) >= 3, "Unstable component")
    require(sum(a + k for a, k in pairs) == 3 * d + g - 1 + len(pairs),
            "Component has the wrong virtual dimension")
    return g, d, tuple(sorted(pairs))


def component_keys(row):
    return {key(code) for t in row["symbolic_terms"] for code in t["monomial"]
            if code[0] <= 1}


def read_report(raw):
    report = json.loads(raw, object_pairs_hook=unique_object)
    fields(report, ["schema_version", "kind", "proof_status", "rows", "components"], "report")
    require(integer(report["schema_version"]) == 1 and
            report["kind"] == "axiomatic_gw.plane_genus_two_components" and
            report["proof_status"] == "candidate_data", "Wrong component schema")
    require(isinstance(report["components"], list) and report["components"], "Empty components")
    stored = set()
    for item in report["components"]:
        fields(item, ["key", "value"], "component")
        q = key(item["key"])
        require(q[0] <= 1 and q not in stored, "Higher-genus or duplicate component")
        rational(item["value"])
        stored.add(q)
    require(isinstance(report["rows"], list), "Expected ancestor rows")
    seen, needed = set(), set()
    for row in report["rows"]:
        fields(row, ["index", "symbolic_terms"], "ancestor row")
        i = integer(row["index"])
        require(6 <= i < 39 and i not in seen, "Invalid or repeated ancestor row")
        seen.add(i)
        require(isinstance(row["symbolic_terms"], list), "Expected symbolic terms")
        for term in row["symbolic_terms"]:
            fields(term, ["coefficient", "monomial"], "symbolic term")
            require(rational(term["coefficient"]) != 0, "Zero symbolic coefficient")
            require(isinstance(term["monomial"], list), "Expected component monomial")
            for code in term["monomial"]:
                key(code)
        needed |= component_keys(row)
    require(seen == set(range(6, 39)), "Incomplete ancestor-row coverage")
    require(stored == needed, "Missing or unused full component key")
    return report


def read_selections(raw, rows):
    """Check full-key cache hints; omitted dependencies keep the original fallback."""
    report = json.loads(raw, object_pairs_hook=unique_object)
    fields(report, ["schema_version", "kind", "proof_status", "rows"], "selections")
    require(integer(report["schema_version"]) == 1 and
            report["kind"] == "axiomatic_gw.plane_elliptic_component_selections" and
            report["proof_status"] == "cache_selection_hint", "Wrong selection schema")
    require(isinstance(report["rows"], list), "Expected selection rows")
    expected = {i for i, row in enumerate(rows) if key(row["key"])[0] == 1 and
                3 <= sum(row["key"][3::2]) <= len(row["key"][2:]) // 2}
    result = {}
    for row in report["rows"]:
        fields(row, ["index", "component", "keys"], "selection row")
        i = integer(row["index"])
        require(i in expected and i not in result, "Invalid or duplicate component selection")
        require(key(row["component"]) == key(rows[i]["key"]), "Changed selected component")
        require(isinstance(row["keys"], list), "Expected selected full keys")
        selected = [key(code) for code in row["keys"]]
        require(len(selected) == len(set(selected)), "Duplicate selected full key")
        power = sum(rows[i]["key"][3::2])
        require(all(g == 0 or (g == 1 and sum(k for _, k in pairs) < power)
                    for g, _, pairs in selected), "Nondecreasing elliptic cache dependency")
        result[i] = selected
    require(set(result) == expected, "Incomplete component selection coverage")
    return result


def header(raw, title, imports, namespace, description):
    return ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            "Authors: JMA", "-/", "module", "",
            *["public import " + name for name in imports], "", "/-!", "# " + title, "",
            *description, "", "Candidate input SHA256: " + hashlib.sha256(raw).hexdigest(),
            "-/", "", "@[expose] public section", "set_option Elab.async false",
            "set_option maxRecDepth 65536", "", "namespace " + namespace,
            "open SurfaceGenusTwo", ""]


def data_lines(rows):
    size = len(rows)
    lines = ["/-- Full lower-genus keys, retaining insertion multiplicities and the curve class. -/",
             f"def key (i : Fin {size}) : SurfaceAncestorKey .plane :=", "  (#["]
    for index, row in enumerate(rows):
        g, d, *pairs = row["key"]
        lines += [f"    ⟨{g}, ![{d}],", "      (["]
        lines += [f"        ⟨{LABELS[pairs[k]]}, {pairs[k + 1]}⟩" +
                  ("," if k + 2 < len(pairs) else "") for k in range(0, len(pairs), 2)]
        lines += ["      ] : List (SurfaceInsertion .plane)), by decide⟩" +
                  ("," if index + 1 < size else "")]
    lines += ["  ] : Array (SurfaceAncestorKey .plane))[i.val]", "",
              "/-- Candidate scalar expressions, accepted only by the computations below. -/",
              f"def entries (i : Fin {size}) : RationalTerms (SurfaceAncestorKey .plane) :=",
              "  RationalTerms.term ((#["]
    for index, row in enumerate(rows):
        a, b = row["value"]
        lines += [f"    ({a} / {b} : ℚ)" + ("," if index + 1 < size else "")]
    return lines + ["  ] : Array ℚ)[i.val]) 0", ""]


def point_source(raw, rows):
    namespace = "AxiomaticGW.GKM." + POINT
    lines = header(raw, "Certified components of the plane point ancestor equation",
                   ["AxiomaticGW.Surfaces.GenusTwoCachedAncestors"], namespace, [
                       "The full degree-one genus-two point ancestor of power three uses these",
                       "21 distinct lower-genus components. Every stored expression is checked",
                       "against the original algorithm; unlisted components retain that algorithm."])
    require(len(rows) == 21, "Changed held point-component frame")
    lines += data_lines(rows) + ["/-- Each full component is stored once. -/",
                               "theorem keys_injective : Function.Injective key := by decide +kernel", ""]
    for i in range(len(rows)):
        lines += [f"private theorem value_{i} : residualTerms (key {i}) = entries {i} := by decide +kernel", ""]
    lines += ["/-- Individually checked values assembled without re-evaluating other entries. -/",
              "theorem computed (i : Fin 21) : residualTerms (key i) = entries i := by",
              "  fin_cases i"]
    lines += [f"  · exact value_{i}" for i in range(21)]
    lines += ["", "/-- The existing cache interface also preserves every unlisted component. -/",
              "def cache : ResidualCache .plane :=",
              "  ResidualCache.ofEntries key entries keys_injective (fun i ↦ (computed i).symm)",
              "", "end " + namespace, ""]
    return "\n".join(lines)


def sources(raw, selections_raw=None):
    report = read_report(raw)
    rows = sorted(report["components"], key=lambda item: item["key"])
    indexed = {key(row["key"]): i for i, row in enumerate(rows)}
    if selections_raw is None:
        selections_raw = SELECTIONS.read_bytes()
    selections = read_selections(selections_raw, rows)
    selected_indices = {i: sorted(indexed[q] for q in selected if q in indexed)
                        for i, selected in selections.items()}
    point_keys = component_keys(next(r for r in report["rows"] if r["index"] == 12))
    point_rows = [row for row in rows if key(row["key"]) in point_keys]
    point_indices = {key(row["key"]): i for i, row in enumerate(point_rows)}
    result = {POINT + ".lean": point_source(raw, point_rows)}
    description = ["Each candidate value is separately checked against the original residual algorithm.",
                   "The symbolic rows only select cache entries; final equations require their own replay."]
    data = header(raw, "Shared lower-genus components of the plane ancestor suite",
                  ["AxiomaticGW.GKM.Fixtures." + POINT,
                   "AxiomaticGW.Surfaces.LowGenusAncestorDimension"], NAMESPACE, description)
    data += data_lines(rows) + ["end " + NAMESPACE, ""]
    result[PREFIX + "Data.lean"] = "\n".join(data)
    groups = {}
    membership = {}
    for i, row in enumerate(rows):
        g, _, pairs = key(row["key"])
        group = f"Genus{g}Psi{sum(k for _, k in pairs)}"
        groups.setdefault(group, []).append(i)
        membership[i] = group
    for group, indices in sorted(groups.items()):
        imports = ["AxiomaticGW.GKM.Fixtures." + PREFIX + "Data"]
        selected_rows = [i for i in indices if i in selected_indices]
        if selected_rows:
            imports += ["AxiomaticGW.Surfaces.GenusTwoCachedComponents"]
            needed = {membership[j] for i in selected_rows for j in selected_indices[i]}
            require(group not in needed, "Circular component cache")
            imports += ["AxiomaticGW.GKM.Fixtures." + PREFIX + name for name in sorted(needed)]
        lines = header(raw, "Certified plane components: " + group,
                       imports, NAMESPACE, description)
        lines += ["namespace " + group, ""]
        if selected_rows:
            lines += ["-- Cache-selection SHA256: " + hashlib.sha256(selections_raw).hexdigest(), ""]
        for i in indices:
            g, _, pairs = q = key(rows[i]["key"])
            above = sum(k for _, k in pairs) > 3 * g - 3 + len(pairs)
            if i in selected_indices:
                selected = selected_indices[i]
                lines += [f"private def indices_{i} (j : Fin {len(selected)}) : Fin {len(rows)} :=",
                          "  (#["]
                lines += ["    " + ", ".join(map(str, selected[j:j + 8])) +
                          ("," if j + 8 < len(selected) else "")
                          for j in range(0, len(selected), 8)]
                lines += [f"  ] : Array (Fin {len(rows)}))[j.val]", "",
                          f"private theorem components_{i} (j : Fin {len(selected)}) :",
                          f"    residualTerms (key (indices_{i} j)) = entries (indices_{i} j) := by",
                          "  fin_cases j"]
                lines += [f"  · exact {membership[j]}.value_{j}" for j in selected]
                lines += ["", f"private def cache_{i} : ResidualCache .plane :=",
                          f"  .ofEntries (key ∘ indices_{i}) (entries ∘ indices_{i}) (by decide +kernel)",
                          f"    (fun j ↦ (components_{i} j).symm)", ""]
            if q not in point_indices and not above:
                lines += ["set_option maxHeartbeats 4000000 in",
                          ("-- Check the original finite ancestor equation at this full component."
                           if i in selected_indices else
                           "-- Check the original finite ancestor recursion at this full component.")]
            lines += [f"theorem value_{i} : residualTerms (key {i}) = entries {i} := by"]
            if q in point_indices:
                j = point_indices[q]
                lines += [f"  change residualTerms ({POINT}.key {j}) = _",
                          f"  rw [{POINT}.computed]", "  decide +kernel"]
            elif above:
                genus = "Zero" if g == 0 else "One"
                branch = "if_pos" if g == 0 else "if_neg"
                lines += [f"  have hz := SurfaceGenus{genus}.ancestorValue_zero_of_cotangent_bound",
                          f"    (key {i}) (by decide +kernel) (by decide +kernel)",
                          "  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),",
                          f"    SurfaceGenusOne.componentValue, {branch} (by decide +kernel), hz]",
                          "  decide +kernel"]
            elif i in selected_indices:
                lines += ["  rw [residualTerms, if_pos (by decide +kernel), if_pos (by decide +kernel),",
                          "    SurfaceGenusOne.componentValue, if_neg (by decide +kernel),",
                          f"    ← ellipticStepCached_eq cache_{i} (key {i})",
                          "      (by decide +kernel) (by decide +kernel)]",
                          "  decide +kernel"]
            else:
                lines += ["  decide +kernel"]
            lines += [""]
        lines += ["end " + group, "end " + NAMESPACE, ""]
        result[PREFIX + group + ".lean"] = "\n".join(lines)
    replay = header(raw, "Certified shared plane components and partial caches",
                    ["AxiomaticGW.GKM.Fixtures." + PREFIX + group for group in sorted(groups)],
                    NAMESPACE, description)
    replay += ["/-- Every stored component is identified with the original algorithm. -/",
               f"theorem computed (i : Fin {len(rows)}) : residualTerms (key i) = entries i := by",
               "  fin_cases i"]
    replay += [f"  · exact {membership[i]}.value_{i}" for i in range(len(rows))]
    replay += ["", "/-- Select a smaller cache while preserving the original fallback at other keys. -/",
               f"def cacheFor {{n : ℕ}} (indices : Fin n → Fin {len(rows)})",
               "    (hinj : Function.Injective (key ∘ indices)) : ResidualCache .plane :=",
               "  .ofEntries (key ∘ indices) (entries ∘ indices) hinj",
               "    (fun i ↦ (computed (indices i)).symm)", "", "end " + NAMESPACE, ""]
    result[PREFIX + "Replay.lean"] = "\n".join(replay)
    caches = header(raw, "Component selections for the original plane ancestor equations",
                    ["AxiomaticGW.GKM.Fixtures." + PREFIX + "Replay"], NAMESPACE, description)
    for row in sorted(report["rows"], key=lambda item: item["index"]):
        i = row["index"]
        indices = sorted(indexed[q] for q in component_keys(row))
        caches += ["-- Numeric suffixes retain the stable external ancestor-row identifiers.",
                   f"/-- Full component indices selected for ancestor row {i}. -/",
                   "@[nolint defsWithUnderscore]",
                   f"def indices_{i} (j : Fin {len(indices)}) : Fin {len(rows)} :=", "  (#["]
        caches += ["    " + ", ".join(map(str, indices[j:j + 8])) +
                   ("," if j + 8 < len(indices) else "") for j in range(0, len(indices), 8)]
        caches += [f"  ] : Array (Fin {len(rows)}))[j.val]", "",
                   f"/-- A proved partial component cache for ancestor row {i}. -/",
                   "@[nolint defsWithUnderscore]",
                   f"def cache_{i} : ResidualCache .plane :=",
                   f"  cacheFor indices_{i} (by decide +kernel)", ""]
    caches += ["end " + NAMESPACE, ""]
    result[PREFIX + "Caches.lean"] = "\n".join(caches)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--selections", type=Path, default=SELECTIONS)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = sources(args.report.read_bytes(), args.selections.read_bytes())
    if not args.check:
        args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = args.output_dir / name
        if args.check:
            require(path.is_file() and path.read_text() == source, "Stale generated file: " + name)
        elif not path.exists() or path.read_text() != source:
            path.write_text(source)


if __name__ == "__main__":
    main()
