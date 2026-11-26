#!/usr/bin/env python3
"""Replay complete shared ancestor equations for the held 48 plane requests.

Preflight checks serialization, closure, descent and arithmetic consistency.
Only the generated Lean proofs identify candidate rows with the original
square/product equations and their canonical low-psi values.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from check_gkm_inputs import integer, rational, require, unique_object
from export_admcycles_certificate import rational_text
from gkm_plane_few_markings import REQUESTS

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "PlaneGenusTwoAncestors"
NAMESPACE = "AxiomaticGW.GKM.PlaneGenusTwoAncestors"
GROUPS = (("LowPsi", 0, 1), ("PsiTwo", 2, 2), ("PsiThree", 3, 3),
          ("PsiFour", 4, 4), ("PsiFive", 5, 5), ("PsiSix", 6, 6))


def fields(value, expected, context):
    require(isinstance(value, dict) and set(value) == set(expected),
            f"Unexpected {context} fields")


def key(code):
    require(isinstance(code, list) and len(code) in (4, 6), "Wrong ancestor key shape")
    code = tuple(integer(n) for n in code)
    require(code[0] == 2 and code[1] in (0, 1), "Wrong ancestor genus or full curve class")
    pairs = tuple(zip(code[2::2], code[3::2]))
    require(all(a in (0, 1, 2) and 0 <= k <= 6 for a, k in pairs),
            "Wrong ancestor basis state or descendant power")
    require(sum(k for _, k in pairs) <= 6, "Ancestor exceeds the fixed suite's psi bound")
    return code[0], code[1], tuple(sorted(pairs))


def psi(q):
    return sum(k for _, k in q[2])


def read_report(raw):
    report = json.loads(raw, object_pairs_hook=unique_object)
    fields(report, ["schema_version", "kind", "proof_status", "ancestor_rows", "requests"],
           "report")
    require(integer(report["schema_version"]) == 1 and
            report["kind"] == "axiomatic_gw.plane_genus_two_ancestor_cache" and
            report["proof_status"] == "candidate_data", "Wrong candidate schema")
    require(isinstance(report["ancestor_rows"], list) and report["ancestor_rows"],
            "Empty ancestor table")
    values = {}
    for row in report["ancestor_rows"]:
        fields(row, ["key", "value", "terms"], "ancestor row")
        q = key(row["key"])
        require(q not in values, "Duplicate complete ancestor key")
        values[q] = rational(row["value"])

    def evaluate(terms, parent=None):
        require(isinstance(terms, list), "Expected complete term list")
        result = Fraction(0)
        for term in terms:
            fields(term, ["coefficient", "monomial"], "term")
            require(isinstance(term["monomial"], list), "Expected monomial list")
            v = rational(term["coefficient"])
            for code in term["monomial"]:
                q = key(code)
                require(q in values, "Missing ancestor dependency")
                if parent is not None:
                    require(psi(q) < psi(parent), "Nondecreasing ancestor dependency")
                v *= values[q]
            result += v
        return result

    for row in report["ancestor_rows"]:
        q = key(row["key"])
        if psi(q) <= 1:
            require(row["terms"] == [], "Low-psi terminal has unexpected boundary terms")
        else:
            require(evaluate(row["terms"], q) == values[q], "Wrong boundary equation value")

    codes = {"unit": 0, "H": 1, "pt": 2}
    expected = [{"genus": 2, "curve": list(beta),
                 "insertions": [[codes[a], k] for a, k in zip(labels, powers)]}
                for beta, powers, labels in REQUESTS["X0"]]
    require(isinstance(report["requests"], list) and len(report["requests"]) == len(expected),
            "Incomplete incoming request coverage")
    for entry, request in zip(report["requests"], expected):
        fields(entry, ["query", "value", "terms"], "incoming request")
        fields(entry["query"], ["genus", "curve", "insertions"], "query")
        q = entry["query"]
        require(isinstance(q["curve"], list) and isinstance(q["insertions"], list),
                "Wrong query containers")
        integer(q["genus"])
        for n in q["curve"]: integer(n)
        for pair in q["insertions"]:
            require(isinstance(pair, list) and len(pair) == 2, "Unpaired query insertion")
            for n in pair: integer(n)
        require(q == request, "Changed complete incoming request")
        require(evaluate(entry["terms"]) == rational(entry["value"]),
                "Wrong descendant equation value")
    return report


def header(raw, imports, title):
    return ["/-", "Copyright (c) 2026 JMA. All rights reserved.",
            "Released under Apache 2.0 license as described in the file LICENSE.",
            "Authors: JMA", "-/", "module", "",
            *["public import " + name for name in imports], "",
            "/-!", "# " + title, "",
            "Input SHA256: " + hashlib.sha256(raw).hexdigest(),
            "Candidate values become certificates only after their full equations are checked.",
            "The original canonical seeds and geometric hypotheses are unchanged.", "-/", "",
            "@[expose] public section", "set_option Elab.async false",
            "set_option maxRecDepth 65536", "", "namespace " + NAMESPACE, "",
            "open BelorousskiPandharipande SurfaceGenusTwo", ""]


def sources(raw):
    report = read_report(raw)
    rows = report["ancestor_rows"]
    size = len(rows)
    indexed = {key(row["key"]): i for i, row in enumerate(rows)}
    labels = [".unit", ".hyperplane", ".point"]

    def lean_key(code):
        _, degree, pairs = key(code)
        insertions = ", ".join(f"⟨{labels[a]}, {k}⟩" for a, k in pairs)
        return f"⟨2, ![{degree}], ([{insertions}] : List (SurfaceInsertion .plane)), by decide⟩"

    def lean_terms(terms):
        rendered = []
        for term in terms:
            variables = ", ".join(f"key {indexed[key(q)]}" for q in term["monomial"])
            monomial = "0" if not variables else "{" + variables + "}"
            rendered.append(f"({rational_text(rational(term['coefficient']))}, {monomial})")
        return "0" if not rendered else "{\n    " + ",\n    ".join(rendered) + "}"

    data = header(raw, ["AxiomaticGW.Surfaces.PlaneGenusTwoAncestorCache",
                        "AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneLine",
                        "AxiomaticGW.GKM.Fixtures.PlaneGenusTwoFewMarkingsData"],
                  "Complete candidate ancestor data for the plane few-marking suite")
    data += ["/-- Every full ancestor key, including degree-zero and vanishing rows. -/",
             f"def key (i : Fin {size}) : SurfaceAncestorKey .plane :=",
             "  (#[" + ",\n    ".join(lean_key(row["key"]) for row in rows) +
             "\n    ] : Array (SurfaceAncestorKey .plane))[i.val]", "",
             "/-- Exact candidate values, interpreted only after table acceptance. -/",
             f"def value (i : Fin {size}) : ℚ :=",
             "  (#[" + ",\n    ".join(rational_text(rational(row["value"])) for row in rows) +
             "] : Array ℚ)[i.val]", ""]
    for i, row in enumerate(rows):
        data += [f"/-- Complete original candidate boundary terms for row {i}. -/",
                 f"def terms_{i} : RationalTerms (SurfaceAncestorKey .plane) :=",
                 "  " + lean_terms(row["terms"]), ""]
    data += ["/-- All original terms, preserving coefficients and repeated occurrences. -/",
             f"def terms (i : Fin {size}) : RationalTerms (SurfaceAncestorKey .plane) :=",
             "  (#[" + ",\n    ".join(f"terms_{i}" for i in range(size)) +
             "] : Array (RationalTerms (SurfaceAncestorKey .plane)))[i.val]", "",
             "/-- The finite cache keeps complete keys; equal energy does not merge queries. -/",
             "def queries : Finset (SurfaceAncestorKey .plane) := Finset.univ.image key", "",
             "/-- Candidate lookup; callers must check membership and table acceptance. -/",
             "def values (q : SurfaceAncestorKey .plane) : ℚ :=",
             f"  (((List.finRange {size}).find? (fun i ↦ key i = q)).map value).getD 0", "",
             "/-- No two rows denote the same full ancestor. -/",
             "theorem keys_injective : Function.Injective key := by decide +kernel", "",
             "/-- Every declared row is returned by the lookup. -/",
             "theorem values_key : ∀ i, values (key i) = value i := by decide +kernel", "",
             "end " + NAMESPACE, ""]
    result = {PREFIX + "Data.lean": "\n".join(data)}
    for group, low, high in GROUPS:
        indices = [i for i, row in enumerate(rows) if low <= psi(key(row["key"])) <= high]
        imports = ["AxiomaticGW.GKM.Fixtures." + PREFIX + "Data"]
        shared_components = 3 <= low <= 5
        if shared_components:
            imports.append("AxiomaticGW.GKM.Fixtures.PlaneGenusTwoComponentsCaches")
            if low == 3:
                imports.append("AxiomaticGW.GKM.Fixtures.PlaneGenusTwoPointAncestor")
        elif low >= 3:
            imports.append("AxiomaticGW.Surfaces.LowGenusAncestorDimension")
        lines = header(raw, imports,
                       "Plane ancestor arithmetic: " + group)
        lines += ["namespace " + group, ""]
        if not shared_components:
            lines += ["attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.vectorLookup",
                      "attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.rationalCached",
                      "attribute [local cbv_eval] PlaneGenusTwoFewMarkingsReplay.ellipticCached", ""]
        if low >= 3 and not shared_components:
            lines += ["-- Proved dimension vanishing avoids expanding impossible lower-genus ancestors.",
                      "attribute [local cbv_eval] SurfaceGenusZero.ancestorValue_pruned",
                      "attribute [local cbv_eval] SurfaceGenusOne.ancestorValue_pruned", ""]
        for i in indices:
            if high <= 1:
                statement = (f"theorem terminal_{i} : value {i} =\n"
                             f"    planeLowPsiValueWith GenusTwoPlaneLine.values (key {i})")
            else:
                statement = (f"theorem reduction_{i} :\n"
                             f"    ancestorReductionTerms (key {i}) (by decide +kernel) = terms {i}")
            if shared_components and i != 12:
                lines += ["set_option maxHeartbeats 4000000 in",
                          "-- Check the full contraction using separately certified components."]
            elif high > 1 and not shared_components:
                lines += ["set_option maxHeartbeats 4000000 in",
                          "-- Replay the complete boundary contraction, including all lower-genus factors.",
                          "set_option cbv.maxSteps 4000000 in"]
            lines += [statement + " := by"]
            if shared_components:
                if i == 12:
                    lines += ["  exact PlaneGenusTwoPointAncestor.reduction", ""]
                else:
                    lines += ["  rw [← ancestorReductionTermsCached_eq",
                              f"    PlaneGenusTwoComponents.cache_{i}]",
                              "  decide +kernel", ""]
            else:
                if high > 1:
                    lines += ["  apply of_decide_eq_true"]
                lines += ["  cbv", ""]
        lines += ["end " + group, "end " + NAMESPACE, ""]
        result[PREFIX + group + ".lean"] = "\n".join(lines)

    assembly = header(raw, ["AxiomaticGW.GKM.Fixtures." + PREFIX + group
                            for group, _, _ in GROUPS],
                      "Accepted shared ancestors for every plane few-marking request")
    for i, row in enumerate(rows):
        power = psi(key(row["key"]))
        group = next(name for name, low, high in GROUPS if low <= power <= high)
        assembly += [f"private theorem row_{i} :",
                     "    checkAncestorRow (planeLowPsiValueWith GenusTwoPlaneLine.values)",
                     f"      queries values (key {i}) = true := by",
                     "  rw [checkAncestorRow, decide_eq_true_eq]",
                     "  refine ⟨by decide +kernel, ?_⟩"]
        if power <= 1:
            assembly += [f"  rw [dif_pos (show (key {i}).totalPsi ≤ 1 by decide +kernel), values_key]",
                         f"  exact {group}.terminal_{i}", ""]
        else:
            assembly += [f"  rw [dif_neg (show ¬(key {i}).totalPsi ≤ 1 by decide +kernel)]",
                         f"  unfold ancestorStep",
                         f"  rw [{group}.reduction_{i}]",
                         "  decide +kernel", ""]
    assembly += ["/-- All rows satisfy their original equations and include every dependency. -/",
                 "theorem accepted :",
                 "    checkAncestorValues (planeLowPsiValueWith GenusTwoPlaneLine.values)",
                 "      queries values = true := by",
                 "  rw [checkAncestorValues, decide_eq_true_eq]",
                 "  intro q hq",
                 "  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq",
                 "  fin_cases i"]
    assembly += [f"  · exact row_{i}" for i in range(size)]
    assembly += ["", "/-- Every cached row agrees with the existing terminating ancestor algorithm. -/",
                 f"theorem values_eq (i : Fin {size}) : value i =",
                 "    planeAncestorValueWith GenusTwoPlaneLine.values (key i) := by",
                 "  rw [← values_key]",
                 "  exact checkAncestorValues_sound _ queries values accepted (key i)",
                 "    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)", "",
                 "/-- The cache preserves every incoming full query, including queries outside it. -/",
                 "theorem query_eq (q : SurfaceQuery .plane) :",
                 "    planeQueryValueCached? GenusTwoPlaneLine.values queries values q =",
                 "      planeQueryValueWith? GenusTwoPlaneLine.values q :=",
                 "  planeQueryValueCached?_eq_with _ queries values accepted q", "",
                 "end " + NAMESPACE, ""]
    result[PREFIX + "Replay.lean"] = "\n".join(assembly)

    computation = header(raw, ["AxiomaticGW.GKM.Fixtures." + PREFIX + "Data"],
                         "Plane descendant arithmetic using the candidate ancestor table")
    computation += ["-- This calculation is conditional on the separately checked ancestor table.",
                    "/-- The original genus-two comparison, preserving each ordered insertion. -/",
                    "def mixedTerms (q : SurfaceQuery .plane) : RationalTerms (SurfaceAncestorKey .plane) :=",
                    "  SurfaceDescendant.mixedAncestorTerms 2 (Fin q.insertions.length)",
                    "    (by simp only [StableArity, Fintype.card_fin]; omega)",
                    "    (List.finRange q.insertions.length) q.beta",
                    "    (fun i ↦ (q.insertions.get i).psi) 0 (fun i ↦ (q.insertions.get i).label)", ""]
    for i, request in enumerate(report["requests"]):
        computation += ["-- Preserve the stable numeric row names used by the certificate exchange.",
                        f"/-- Candidate comparison terms for the complete held request {i}. -/",
                        "@[nolint defsWithUnderscore]",
                        f"def comparisonTerms_{i} : RationalTerms (SurfaceAncestorKey .plane) :=",
                        "  " + lean_terms(request["terms"]), "",
                        "/-- Check the expansion before evaluating any candidate ancestor values. -/",
                        f"theorem comparison_{i} :",
                        f"    mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests {i}) =",
                        f"      comparisonTerms_{i} := by decide +kernel", "",
                        f"private theorem cached_{i} :",
                        "    planeQueryValueCached? GenusTwoPlaneLine.values queries values",
                        f"      (PlaneGenusTwoFewMarkingsReplay.requests {i}) =",
                        f"      some (PlaneGenusTwoFewMarkingsReplay.values {i}) := by",
                        "  change some (RationalTerms.eval (ancestorValueCached",
                        "    (planeLowPsiValueWith GenusTwoPlaneLine.values) queries values)",
                        f"    (mixedTerms (PlaneGenusTwoFewMarkingsReplay.requests {i}))) = _",
                        f"  rw [comparison_{i}]",
                        "  decide +kernel", ""]
    computation += ["/-- Every full incoming request is evaluated using the declared candidate cache. -/",
                    "theorem cached_computation (i : Fin 48) :",
                    "    planeQueryValueCached? GenusTwoPlaneLine.values queries values",
                    "      (PlaneGenusTwoFewMarkingsReplay.requests i) =",
                    "      some (PlaneGenusTwoFewMarkingsReplay.values i) := by",
                    "  fin_cases i"]
    computation += [f"  · exact cached_{i}" for i in range(48)]
    computation += ["", "end " + NAMESPACE, ""]
    result[PREFIX + "Descendants.lean"] = "\n".join(computation)

    replay = header(raw, ["AxiomaticGW.GKM.Fixtures." + PREFIX + "Replay",
                         "AxiomaticGW.GKM.Fixtures." + PREFIX + "Descendants"],
                    "Full plane few-marking claims from the certified ancestor cache")
    replay += ["/-- All 48 original queries follow from both accepted tables and the original algorithm. -/",
               "theorem descendants_accepted (i : Fin 48) :",
               "    planeQueryValue? (PlaneGenusTwoFewMarkingsReplay.requests i) =",
               "      some (PlaneGenusTwoFewMarkingsReplay.values i) := by",
               "  rw [← planeQueryValueCached?_eq 1 GenusTwoPlaneLine.values GenusTwoPlaneLine.accepted",
               "    queries values accepted (PlaneGenusTwoFewMarkingsReplay.requests i)",
               "    (by revert i; decide +kernel)]",
               "  exact cached_computation i", "",
               "end " + NAMESPACE, ""]
    result[PREFIX + "DescendantReplay.lean"] = "\n".join(replay)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, source in sources(args.report.read_bytes()).items():
        path = args.output_dir / name
        if args.check:
            require(path.read_text() == source, f"Changed generated source: {path}")
        elif not path.exists() or path.read_text() != source:
            path.write_text(source)


if __name__ == "__main__":
    main()
