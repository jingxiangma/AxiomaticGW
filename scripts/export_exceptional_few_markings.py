#!/usr/bin/env python3
"""Export point-supported exceptional rows of the fixed genus-two few-marking manifest."""
import argparse
import hashlib
import json
from pathlib import Path

from genus_two_few_marking_requests import manifest
from gkm_genus_two_degree_zero import query_text

ROOT = Path(__file__).resolve().parents[1]
FRAME = ROOT / "environments/genus-two-few-markings-requests.json"
OUTPUT = ROOT / "AxiomaticGW/Surfaces/Fixtures/GenusTwoExceptionalFewMarkings.lean"


def source():
    raw = FRAME.read_bytes()
    frame = json.loads(raw)
    if frame != manifest():
        raise ValueError("The saved query corpus differs from the full benchmark enumeration")
    lines = ["module", "", "public import AxiomaticGW.Surfaces.ExceptionalEvaluationSupport",
             "public import AxiomaticGW.Surfaces.GenusTwoFewMarkings", "", "/-!",
             "# Point-supported exceptional requests in the fixed few-marking corpus", "",
             "Frame SHA256: " + hashlib.sha256(raw).hexdigest(),
             "The ordinary vanishing proof uses the geometric point-pullback support law.",
             "Each literal retains its full class, original marking order and cotangent powers.", "-/", "",
             "@[expose] public section", "namespace AxiomaticGW.GenusTwoExceptionalFewMarkings",
             "open SurfaceGenusTwo", "", "set_option Elab.async false",
             "-- Elaborate the literal 514-row array in the two-point blowup frame.",
             "set_option maxRecDepth 8192", ""]
    for target, ns, surface, size in (("X1", "OneBlowup", "hirzebruchOne", 106),
                                      ("X2", "TwoBlowups", "blowupTwo", 514)):
        target_frame = next(t for t in frame["targets"] if t["target"] == target)
        rows = [q for q in target_frame["requests"]
                if q["class"][-1] == 0 and any(q["class"]) and "pt" in q["labels"]]
        if len(rows) != size:
            raise ValueError(f"Unexpected number of point-supported exceptional queries on {target}")
        requests = [query_text(q) for q in rows]
        lines += [f"namespace {ns}", "",
                  "/-- Complete ordered requests selected from the fixed corpus in file order. -/",
                  f"def requests (i : Fin {size}) : SurfaceQuery .{surface} :=",
                  "  (#[" + ",\n    ".join(requests) + f"] :\n    Array (SurfaceQuery .{surface}))[i.val]'i.isLt", "",
                  "/-- Every literal is an admissible benchmark with a zero point-supported evaluation. -/",
                  "theorem accepted : ∀ i, FewMarkingQuery (requests i) ∧",
                  "    exceptionalPointQueryValue? (requests i) = some 0 := by",
                  "  unfold FewMarkingQuery", "  decide +kernel", "",
                  "/-- Under exceptional point-pullback support, every requested GW evaluation vanishes. -/",
                  "theorem geometric {C : StableCurveCohomology ℚ}",
                  f"    {{Omega : GromovWittenTheory ℚ (SurfaceCohomology SurfaceTarget.{surface}.blowups)",
                  f"      SurfaceTarget.{surface}.Curve SurfaceTarget.{surface}.effective C}}",
                  "    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}",
                  "    {U : UnstableDescendantConventions M I}",
                  f"    (G : StableMapIntersection U) (hG : ExceptionalPointSupport G) (i : Fin {size}) :",
                  "    (requests i).checkedEval U = some 0 :=",
                  "  exceptionalPointQueryValue?_sound G hG _ _ (accepted i).2", "",
                  f"end {ns}", ""]
    return "\n".join(lines + ["end AxiomaticGW.GenusTwoExceptionalFewMarkings", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = source()
    if args.check:
        if args.output.read_text() != rendered:
            parser.exit(1, "Saved exceptional query certificate differs from regenerated source\n")
    else:
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
